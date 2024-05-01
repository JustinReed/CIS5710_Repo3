`timescale 1ns / 1ns

// registers are 32 bits in RV32
`define REG_SIZE 31:0

// insns are 32 bits in RV32IM
`define INSN_SIZE 31:0

// RV opcodes are 7 bits
`define OPCODE_SIZE 6:0

`ifndef RISCV_FORMAL
`include "../hw2b/cla.sv"
`include "../hw3-singlecycle/RvDisassembler.sv"
`include "../hw4-multicycle/divider_unsigned_pipelined.sv"
`endif

module Disasm #(
    byte PREFIX = "D"
) (
    input wire [31:0] insn,
    output wire [(8*32)-1:0] disasm
);
  // synthesis translate_off
  // this code is only for simulation, not synthesis
  string disasm_string;
  always_comb begin
    disasm_string = rv_disasm(insn);
  end
  // HACK: get disasm_string to appear in GtkWave, which can apparently show only wire/logic. Also,
  // string needs to be reversed to render correctly.
  genvar i;
  for (i = 3; i < 32; i = i + 1) begin : gen_disasm
    assign disasm[((i+1-3)*8)-1-:8] = disasm_string[31-i];
  end
  assign disasm[255-:8] = PREFIX;
  assign disasm[247-:8] = ":";
  assign disasm[239-:8] = " ";
  // synthesis translate_on
endmodule

module RegFile (
    input logic [4:0] rd,
    input logic [`REG_SIZE] rd_data,
    input logic [4:0] rs1,
    output logic [`REG_SIZE] rs1_data,
    input logic [4:0] rs2,
    output logic [`REG_SIZE] rs2_data,

    input logic clk,
    input logic we,
    input logic rst
);
  localparam int NumRegs = 32;
  // genvar i;
  logic [`REG_SIZE] regs[NumRegs];

  // TODO: your code here
  assign regs[0] = 32'd0; // x0 is always zero
  assign rs1_data = regs[rs1]; // 1st read port
  assign rs2_data = regs[rs2]; // 2nd read port

  genvar i;
  for (i = 1; i < 32; i = i + 1) begin: reg_i
    always_ff @(posedge clk) begin
      if (rst) begin
        regs[i] <= 32'd0;
      end else begin
        if (we == 1 && rd == i) begin
          regs[i] <= rd_data;
        end
      end
    end
  end

endmodule

/**
 * This enum is used to classify each cycle as it comes through the Writeback stage, identifying
 * if a valid insn is present or, if it is a stall cycle instead, the reason for the stall. The
 * enum values are mutually exclusive: only one should be set for any given cycle. These values
 * are compared against the trace-*.json files to ensure that the datapath is running with the
 * correct timing.
 *
 * You will need to set these values at various places within your pipeline, and propagate them
 * through the stages until they reach Writeback where they can be checked.
 */
typedef enum {
  /** invalid value, this should never appear after the initial reset sequence completes */
  CYCLE_INVALID = 0,
  /** a stall cycle that arose from the initial reset signal */
  CYCLE_RESET = 1,
  /** not a stall cycle, a valid insn is in Writeback */
  CYCLE_NO_STALL = 2,
  /** a stall cycle that arose from a taken branch/jump */
  CYCLE_TAKEN_BRANCH = 4,

  // the values below are only needed in HW5B

  /** a stall cycle that arose from a load-to-use stall */
  CYCLE_LOAD2USE = 8,
  /** a stall cycle that arose from a div/rem-to-use stall */
  CYCLE_DIV2USE = 16,
  /** a stall cycle that arose from a fence.i insn */
  CYCLE_FENCEI = 32
} cycle_status_e;

/** state at the start of Decode stage */
typedef struct packed {
  logic [`REG_SIZE] d_pc;
  logic [31:0] d_pc_last;
  logic [`INSN_SIZE] d_insn;
  cycle_status_e d_cycle_status;
} stage_decode_t;

/** state at the start of Execute stage */
typedef struct packed {
  logic [`REG_SIZE] x_pc;
  logic [31:0] x_pc_last;
  logic [`INSN_SIZE] x_insn;
  logic [31:0] x_alu_input1;
  logic [31:0] x_alu_input2;
  logic [31:0] x_store_data;
  logic [4:0] x_alu_input1_adr;
  logic [4:0] x_alu_input2_adr;
  logic [4:0] x_alu_result_adr;
  logic [4:0] x_store_data_rf_adr;
  logic x_halt;
  cycle_status_e x_cycle_status;
} stage_execute_t;

/** state at the start of Memory stage */
typedef struct packed {
  logic [`REG_SIZE] m_pc;
  logic [`INSN_SIZE] m_insn;
  logic [31:0] m_alu_result;
  logic [31:0] m_rs2;
  logic [31:0] m_store_data;
  logic [4:0] m_alu_result_adr;
  logic m_branch_decide;
  logic [31:0] m_branch_result;
  logic m_div_sign_bit;
  logic m_rem_sign_bit;
  logic m_halt;
  cycle_status_e m_cycle_status;
} stage_memory_t;

/** state at the start of Writeback stage */
typedef struct packed {
  logic [`REG_SIZE] w_pc;
  logic [`INSN_SIZE] w_insn;
  logic [31:0] w_alu_result;
  logic [31:0] w_div_alu_result;
  logic [31:0] w_mem_result;
  logic [4:0] w_alu_result_adr;
  logic w_halt;
  cycle_status_e w_cycle_status;
} stage_writeback_t;



module DatapathPipelined (
    input wire clk,
    input wire rst,
    output logic [`REG_SIZE] pc_to_imem,
    input wire [`INSN_SIZE] insn_from_imem,
    // dmem is read/write
    output logic [`REG_SIZE] addr_to_dmem,
    input wire [`REG_SIZE] load_data_from_dmem,
    output logic [`REG_SIZE] store_data_to_dmem,
    output logic [3:0] store_we_to_dmem,

    output logic halt,

    // The PC of the insn currently in Writeback. 0 if not a valid insn.
    output logic [`REG_SIZE] trace_writeback_pc,
    // The bits of the insn currently in Writeback. 0 if not a valid insn.
    output logic [`INSN_SIZE] trace_writeback_insn,
    // The status of the insn (or stall) currently in Writeback. See cycle_status_e enum for valid values.
    output cycle_status_e trace_writeback_cycle_status
);

  // opcodes - see section 19 of RiscV spec
  localparam bit [`OPCODE_SIZE] OpcodeLoad = 7'b00_000_11;
  localparam bit [`OPCODE_SIZE] OpcodeStore = 7'b01_000_11;
  localparam bit [`OPCODE_SIZE] OpcodeBranch = 7'b11_000_11;
  localparam bit [`OPCODE_SIZE] OpcodeJalr = 7'b11_001_11; // comment out for autograder
  // localparam bit [`OPCODE_SIZE] OpcodeMiscMem = 7'b00_011_11;
  localparam bit [`OPCODE_SIZE] OpcodeJal = 7'b11_011_11;

  localparam bit [`OPCODE_SIZE] OpcodeRegImm = 7'b00_100_11;
  localparam bit [`OPCODE_SIZE] OpcodeRegReg = 7'b01_100_11;
  localparam bit [`OPCODE_SIZE] OpcodeEnviron = 7'b11_100_11;

  localparam bit [`OPCODE_SIZE] OpcodeAuipc = 7'b00_101_11;
  localparam bit [`OPCODE_SIZE] OpcodeLui = 7'b01_101_11;

  // cycle counter, not really part of any stage but useful for orienting within GtkWave
  // do not rename this as the testbench uses this value
  logic [`REG_SIZE] cycles_current;
  always_ff @(posedge clk) begin
    if (rst) begin
      cycles_current <= 0;
    end else begin
      cycles_current <= cycles_current + 1;
    end
  end


  /***************/
  /* FETCH STAGE */
  /***************/


  // pc_last_restore: addr+0
  // pc_last: addr+4
  // pc_current: addr+8
  logic [`REG_SIZE] f_pc_current;
  logic [31:0] f_pc_last;
  // logic [31:0] f_pc_last_restore; // necessary in case of a stall
  wire [`REG_SIZE] f_insn;
  cycle_status_e f_cycle_status;

  
  // program counter
  always_ff @(posedge clk) begin
    if (rst) begin
      f_pc_current <= 32'd0;
      f_pc_last <= 32'd0;
      // f_pc_last_restore <= 32'd0;
      // NB: use CYCLE_NO_STALL since this is the value that will persist after the last reset cycle
      f_cycle_status <= CYCLE_NO_STALL;
    end else begin
      f_cycle_status <= CYCLE_NO_STALL;
      // f_pc_last_restore <= f_pc_last;
      f_pc_last <= (d_stall || MX_stall) ? f_pc_last : f_pc_current;
      f_pc_current <= branch_decide ? alt_PC : ((d_stall || MX_stall) ? f_pc_current : (f_pc_current + 4));
    end
  end
  // send PC to imem
  // decide whether or not to repeat instruction if there was a stall in decode stage
  // assign pc_to_imem = load_use ? f_pc_last : f_pc_current;
  assign pc_to_imem = f_pc_current;
  assign f_insn = insn_from_imem;

  // wire [31:0] f_pc_last_fin;
  // wire [31:0] f_pc_curr_fin;
  // assign f_pc_last_fin = load_use ? f_pc_last_restore : f_pc_last;
  // assign f_pc_curr_fin = load_use ? f_pc_last : f_pc_current; 

  // Here's how to disassemble an insn into a string you can view in GtkWave.
  // Use PREFIX to provide a 1-character tag to identify which stage the insn comes from.
  Disasm #(
      .PREFIX("F")
  ) disasm_0fetch (
      .insn  (f_insn),
      .disasm()
  );

  /****************/
  /* DECODE STAGE */
  /****************/

  // this shows how to package up state in a `struct packed`, and how to pass it between stages
  stage_decode_t decode_state;
  always_ff @(posedge clk) begin
    if (rst) begin
      decode_state <= '{
        d_pc: 0,
        d_pc_last: 0,
        d_insn: 0,
        d_cycle_status: CYCLE_RESET
      };
    end else begin
      begin
        decode_state <= '{
          d_pc: branch_decide ? 0 : ((d_stall || MX_stall) ? decode_state.d_pc : f_pc_current),
          d_pc_last: branch_decide ? 0 : ((d_stall || MX_stall)  ? decode_state.d_pc_last : f_pc_last),
          d_insn: branch_decide ? 0 : ((d_stall || MX_stall) ? decode_state.d_insn : f_insn),
          d_cycle_status: branch_decide ? CYCLE_TAKEN_BRANCH : f_cycle_status
        };
      end
    end
  end
  Disasm #(
      .PREFIX("D")
  ) disasm_1decode (
      .insn  (decode_state.d_insn),
      .disasm()
  );

  // TODO: your code here, though you will also need to modify some of the code above
  // TODO: the testbench requires that your register file instance is named `rf`

  // Reg file, read-only during decode stage, write-only during writeback stage. Write after read
  wire [31:0] rs1_out;
  wire [31:0] rs2_out;
  RegFile rf(.rd(w_insn_rd),
    .rd_data(insn_result), // 32b input signal, value to be written
    .rs1(d_insn_rs1), // 5-bit address of value 1 register
    .rs1_data(rs1_out), // 32b output signal, value 1 read
    .rs2(d_insn_rs2), // 5-bit address of value 2 register
    .rs2_data(rs2_out), // 32b output signal, value 2 read

    .clk(clk),
    .we(we_sig),
    .rst(rst));



  // decode all the information from the instruction assuming R-type
  wire [6:0] d_insn_funct7;
  wire [4:0] d_insn_rs2;
  wire [4:0] d_insn_rs1;
  wire [2:0] d_insn_funct3;
  wire [4:0] d_insn_rd;
  wire [6:0] d_insn_opcode;

  // split R-type instruction - see section 2.2 of RiscV spec
  assign {d_insn_funct7, d_insn_rs2, d_insn_rs1, d_insn_funct3, d_insn_rd, d_insn_opcode} = decode_state.d_insn;

  // info for i type instruction
  wire [11:0] imm_i;
  wire [31:0] imm_i_sext;

  assign imm_i = decode_state.d_insn[31:20];  
  assign imm_i_sext = {{20{imm_i[11]}}, imm_i[11:0]};

  // info for u type instruction
  wire [19:0] imm_u;
  assign imm_u = decode_state.d_insn[31:12];

  // info for j type instruction
  wire [20:0] imm_j;
  assign {imm_j[20], imm_j[10:1], imm_j[11], imm_j[19:12], imm_j[0]} = {decode_state.d_insn[31:12], 1'b0};
  wire [`REG_SIZE] imm_j_sext = {{11{imm_j[20]}}, imm_j[20:0]};

  // info for s type instruction
  wire [11:0] imm_s;
  assign imm_s[11:5] = d_insn_funct7, imm_s[4:0] = d_insn_rd;
  wire [`REG_SIZE] imm_s_sext = {{20{imm_s[11]}}, imm_s[11:0]};

  logic [31:0] ALU_input1;
  logic [31:0] ALU_input2;
  logic [31:0] store_data;
  logic [4:0] ALU_input1_adr;
  logic [4:0] ALU_input2_adr;
  logic [4:0] ALU_result_adr;
  logic [4:0] store_data_rf_adr; // location of value in register file being stored
  logic halt_start; // begin process of halting cpu, finish in-flight instructions
  always_comb begin
    case (d_insn_opcode)
      OpcodeLui: begin
        ALU_input1 = {{12{imm_u[19]}}, imm_u[19:0]};
        ALU_input2 = 12;

        ALU_input1_adr = 0; // default assign to x0, which never changes
        ALU_input2_adr = 0;
        ALU_result_adr = d_insn_rd;
      end

      OpcodeAuipc: begin
        ALU_input1 = decode_state.d_pc;
        ALU_input2 = {{12{imm_u[19]}}, imm_u[19:0]} << 12;

        ALU_input1_adr = 0; // default assign to x0, which never changes
        ALU_input2_adr = 0;
        ALU_result_adr = d_insn_rd;
      end

      OpcodeRegImm: begin
        ALU_input1_adr = d_insn_rs1; 
        ALU_input2_adr = 0; // default to x0
        ALU_result_adr = d_insn_rd;
        case(d_insn_funct3)
          3'b000: begin // addi
            ALU_input1 = rs1_out; 
            ALU_input2 = imm_i_sext; // ALU_input2 is imm
          end
          3'b010: begin // slti
            ALU_input1 = rs1_out; 
            ALU_input2 = imm_i_sext; // ALU_input2 is imm
          end
            
          3'b011: begin // sltiu
            ALU_input1 = rs1_out; 
            ALU_input2 = $unsigned(imm_i_sext); // take unsigned version
          end

          3'b100: begin // xori
            ALU_input1 = rs1_out;
            ALU_input2 = imm_i_sext;
          end

          3'b110: begin // ori
            ALU_input1 = rs1_out;
            ALU_input2 = imm_i_sext;
          end

          3'b111: begin // andi
            ALU_input1 = rs1_out;
            ALU_input2 = imm_i_sext;
          end

          3'b001: begin // slli
            ALU_input1 = rs1_out;
            ALU_input2 = {27'b0, imm_i[4:0]};
          end

          3'b101: begin // srli and srai
            ALU_input1 = rs1_out;
            ALU_input2 = {27'b0, imm_i[4:0]};
          end

          default: begin
            ALU_input1 = 0;
            ALU_input2 = 0;
          end
        endcase
      end

      OpcodeRegReg: begin // instructions involving 2 regs
        ALU_input1_adr = d_insn_rs1; 
        ALU_input2_adr = d_insn_rs2;
        ALU_result_adr = d_insn_rd;
        case (d_insn_funct3)
          3'b000: begin // add and sub
            case (d_insn_funct7)
              7'b0000000: begin // add
                ALU_input1 = rs1_out;
                ALU_input2 = rs2_out;
              end
              7'b0100000: begin // sub
                ALU_input1 = rs1_out;
                // ALU_input2 = (32'b11111111111111111111111111111111 ^ rs2_out) + 1;
                ALU_input2 = rs2_out;
              end
              7'b0000001: begin // mul
                ALU_input1 = rs1_out;
                ALU_input2 = rs2_out;
              end
              default: begin
                ALU_input1 = 0;
                ALU_input2 = 0;
              end
            endcase
          end

          3'b001: begin // sll and mulh
            case (d_insn_funct7)
              7'b0000000: begin // sll
                ALU_input1 = rs1_out;
                ALU_input2 = {27'b0, rs2_out[4:0]};
              end

              7'b0000001: begin // mulh
                ALU_input1 = $signed(rs1_out);
                ALU_input2 = $signed(rs2_out);
              end
              default: begin
                ALU_input1 = 0;
                ALU_input2 = 0;
              end
            endcase
          end

          3'b010: begin // slt and mulhsu     
            case (d_insn_funct7)
              7'b0000000: begin // slt
                ALU_input1 = $signed(rs1_out);
                ALU_input2 = $signed(rs2_out);
              end

              7'b0000001: begin // mulhsu
                // if rs2 is negative (31st bit is 1), then 2C it. Otherwise, keep it the same
                ALU_input1 = rs1_out;
                // ALU_input1 = (rs1_out[31] == 1'b1) ? ((32'b11111111111111111111111111111111 ^ rs1_out) + 1) : $unsigned(rs1_out);
                ALU_input2 = rs2_out;
              end

              default: begin
                ALU_input1 = 0;
                ALU_input2 = 0;
              end
            endcase 
          end

          3'b011: begin // sltu and mulhu
            case (d_insn_funct7)
              7'b0000000: begin // sltu
                ALU_input1 = rs1_out;
                ALU_input2 = $unsigned(rs2_out);
              end

              7'b0000001: begin // mulhu
                ALU_input1 = $unsigned(rs1_out);
                ALU_input2 = $unsigned(rs2_out);
              end
              default: begin
                ALU_input1 = 0;
                ALU_input2 = 0;
              end
            endcase
          end

          3'b100: begin // xor & div  
            case (d_insn_funct7)
              7'b0000000: begin // xor
                ALU_input1 = rs1_out;
                ALU_input2 = rs2_out;
              end

              7'b0000001: begin // div
                ALU_input1 = (rs1_out[31] == 1'b1) ? ((32'b11111111111111111111111111111111 ^ rs1_out) + 1) : $unsigned(rs1_out);
                ALU_input2 = (rs2_out[31] == 1'b1) ? ((32'b11111111111111111111111111111111 ^ rs2_out) + 1) : $unsigned(rs2_out);
              end
              default: begin
                ALU_input1 = 0;
                ALU_input2 = 0;
              end
            endcase
          end

          3'b101: begin // srl, divu, and sra
            case (d_insn_funct7)
              7'b0000000: begin // srl
                ALU_input1 = rs1_out;
                ALU_input2 = {27'b0, rs2_out[4:0]};
              end

              7'b0000001: begin // divu
                ALU_input1 = rs1_out;
                ALU_input2 = rs2_out;
              end

              7'b0100000: begin // sra
                ALU_input1 = rs1_out;
                ALU_input2 = {27'b0, rs2_out[4:0]};
              end

              default: begin
                ALU_input1 = 0;
                ALU_input2 = 0;
              end
            endcase
          end

          3'b110: begin // or & rem
            case (d_insn_funct7)
              7'b0000000: begin // or
                ALU_input1 = rs1_out;
                ALU_input2 = rs2_out;
              end

              7'b0000001: begin // rem
                ALU_input1 = (rs1_out[31] == 1'b1) ? ((32'b11111111111111111111111111111111 ^ rs1_out) + 1) : $unsigned(rs1_out);
                ALU_input2 = (rs2_out[31] == 1'b1) ? ((32'b11111111111111111111111111111111 ^ rs2_out) + 1) : $unsigned(rs2_out);
              end

              default: begin
                ALU_input1 = 0;
                ALU_input2 = 0;
              end
            endcase
          end

          3'b111: begin // and & remu
            case (d_insn_funct7)
              7'b0000000: begin // and
                ALU_input1 = rs1_out;
                ALU_input2 = rs2_out;
              end

              7'b0000001: begin // remu
                ALU_input1 = rs1_out;
                ALU_input2 = rs2_out;
              end

              default: begin
                ALU_input1 = 0;
                ALU_input2 = 0;
              end
            endcase
          end

          default: begin
            ALU_input1 = 0;
            ALU_input2 = 0;
          end
        endcase
      end

      OpcodeBranch: begin
        ALU_input1_adr = d_insn_rs1; 
        ALU_input2_adr = d_insn_rs2;
        ALU_result_adr = 0;
        case (d_insn_funct3)
          3'b000: begin // beq
            ALU_input1 = rs1_out;
            ALU_input2 = rs2_out;
          end

          3'b001: begin // bne
            ALU_input1 = rs1_out;
            ALU_input2 = rs2_out;
          end

          3'b100: begin // blt
            ALU_input1 = $signed(rs1_out);
            ALU_input2 = $signed(rs2_out);
          end

          3'b101: begin // bge
            ALU_input1 = $signed(rs1_out);
            ALU_input2 = $signed(rs2_out);
          end

          3'b110: begin // bltu
            ALU_input1 = $unsigned(rs1_out);
            ALU_input2 = $unsigned(rs2_out);
          end

          3'b111: begin // bgeu
            ALU_input1 = $unsigned(rs1_out);
            ALU_input2 = $unsigned(rs2_out);
          end

          default: begin
            ALU_input1 = 0;
            ALU_input2 = 0;
          end
        endcase
      end

      OpcodeJal: begin
        ALU_input1_adr = 0; 
        ALU_input2_adr = 0;
        ALU_result_adr = d_insn_rd;
        ALU_input1 = decode_state.d_pc; // compute branch using alu since add is high num of bits
        ALU_input2 = imm_j_sext;
      end

      OpcodeJalr: begin
        ALU_input1_adr = d_insn_rs1; 
        ALU_input2_adr = 0;
        ALU_result_adr = d_insn_rd;
        ALU_input1 = rs1_out; // compute branch using alu since add is high num of bits
        ALU_input2 = imm_i_sext;
      end

      OpcodeLoad: begin
        // same as OpcodeRegImm
        ALU_input1_adr = d_insn_rs1; 
        ALU_input2_adr = 0; // default to x0
        ALU_result_adr = d_insn_rd;
        ALU_input1 = rs1_out;
        ALU_input2 = imm_i_sext;
      end

      OpcodeStore: begin
        ALU_input1_adr = d_insn_rs1; 
        ALU_input2_adr = 0; // default to x0
        ALU_result_adr = 0; // no ALU result
        store_data_rf_adr = d_insn_rs2;
        ALU_input1 = rs1_out;
        ALU_input2 = imm_s_sext;
        store_data = WD_store_data_bypass ? insn_result : rs2_out;
      end

      OpcodeEnviron: begin
        halt_start = 1;
      end

      default: begin
        ALU_input1 = 0;
        ALU_input2 = 0;
        halt_start = 0;
        ALU_result_adr = 0;
        store_data = 0;
        store_data_rf_adr = 0;
      end
    endcase
  end

  // control logic: decide whether to use value taken from rf or from write-back in case of wd bypass
  wire WD1_bypass;
  wire WD2_bypass;

  assign WD1_bypass = ((writeback_state.w_alu_result_adr == ALU_input1_adr) && ALU_input1_adr != 0);
  assign WD2_bypass = ((writeback_state.w_alu_result_adr == ALU_input2_adr) && ALU_input2_adr != 0);

  wire WD_store_data_bypass;

  assign WD_store_data_bypass = (writeback_state.w_alu_result_adr == store_data_rf_adr) && ALU_input1_adr != 0;


  

  wire [31:0] d_alu_input1_fin;
  wire [31:0] d_alu_input2_fin;

  // assign d_alu_input1_fin = WD1_bypass ? writeback_state.w_alu_result : ALU_input1;
  // assign d_alu_input2_fin = WD2_bypass ? writeback_state.w_alu_result : ALU_input2;
  assign d_alu_input1_fin = WD1_bypass ? insn_result : ALU_input1;
  assign d_alu_input2_fin = WD2_bypass ? insn_result : ALU_input2;

  // check for load-to-use
  wire load_use1;
  assign load_use1 = (x_is_load && (x_insn_rd == ALU_input1_adr) && ALU_input1_adr != 0 && (d_insn_opcode != OpcodeStore));

  wire load_use2;
  assign load_use2 = (x_is_load && (x_insn_rd == ALU_input2_adr) && ALU_input2_adr != 0 && (d_insn_opcode != OpcodeStore));

  wire load_use;
  assign load_use = load_use1 || load_use2;

  wire div_use1;
  assign div_use1 = (x_is_div && (x_insn_rd == ALU_input1_adr) && ALU_input1_adr != 0);

  wire div_use2;
  assign div_use2 = (x_is_div && (x_insn_rd == ALU_input2_adr) && ALU_input2_adr != 0);


  wire d_stall;
  assign d_stall = load_use || x_is_div;


  /*****************/
  /* EXECUTE STAGE */
  /*****************/

  stage_execute_t execute_state;
  always_ff @(posedge clk) begin
    if (rst) begin
      execute_state <= '{
        x_pc: 0,
        x_pc_last: 0,
        x_insn: 0,
        x_alu_input1: 0,
        x_alu_input2: 0,
        x_store_data: 0,
        x_alu_input1_adr: 0,
        x_alu_input2_adr: 0,
        x_alu_result_adr: 0,
        x_store_data_rf_adr: 0,
        x_halt: 0,
        x_cycle_status: CYCLE_RESET
      };
    end else begin
      begin
        execute_state <= '{
          x_pc: branch_decide || d_stall ? 0 : (MX_stall ? execute_state.x_pc : decode_state.d_pc),
          x_pc_last: branch_decide || d_stall ? 0 : (MX_stall ? execute_state.x_pc_last : decode_state.d_pc_last),
          x_insn: branch_decide || d_stall ? 0 : (MX_stall ? execute_state.x_insn : decode_state.d_insn),
          x_alu_input1: branch_decide || d_stall ? 0 : (MX_stall ? execute_state.x_alu_input1 : d_alu_input1_fin),
          x_alu_input2: branch_decide || d_stall ? 0 : (MX_stall ? execute_state.x_alu_input2 : d_alu_input2_fin),
          x_store_data: branch_decide || d_stall ? 0 : (MX_stall ? execute_state.x_store_data : store_data),
          x_alu_input1_adr: branch_decide || d_stall ? 0 : (MX_stall ? execute_state.x_alu_input1_adr : ALU_input1_adr),
          x_alu_input2_adr: branch_decide || d_stall ? 0 : (MX_stall ? execute_state.x_alu_input2_adr : ALU_input2_adr),
          x_alu_result_adr: branch_decide || d_stall ? 0 : (MX_stall ? execute_state.x_alu_result_adr : ALU_result_adr),
          x_store_data_rf_adr: branch_decide || d_stall ? 0 : (MX_stall ? execute_state.x_store_data_rf_adr : store_data_rf_adr),
          x_halt: halt_start,
          x_cycle_status: branch_decide ? CYCLE_TAKEN_BRANCH : decode_state.d_cycle_status
        };
      end
    end
  end

  Disasm #(
      .PREFIX("X")
  ) disasm_2execute (
      .insn  (execute_state.x_insn),
      .disasm()
  );

  // get information from instruction
  wire [6:0] x_insn_funct7;
  wire [4:0] x_insn_rs2; // not used in this stage
  wire [4:0] x_insn_rs1; // not used in this stage
  wire [2:0] x_insn_funct3;
  wire [4:0] x_insn_rd; // not used in this stage
  wire [6:0] x_insn_opcode;

  // split R-type instruction - see section 2.2 of RiscV spec
  assign {x_insn_funct7, x_insn_rs2, x_insn_rs1, x_insn_funct3, x_insn_rd, x_insn_opcode} = execute_state.x_insn;

  // for computing branch targets
  logic [31:0] alt_PC;

  wire [12:0] imm_b;
  wire [31:0] imm_b_sext;
  assign {imm_b[12], imm_b[10:5]} = x_insn_funct7, {imm_b[4:1], imm_b[11]} = x_insn_rd, imm_b[0] = 1'b0;
  assign imm_b_sext = {{19{imm_b[12]}}, imm_b[12:0]};

  wire x_is_store_op;
  assign x_is_store_op = (x_insn_opcode == OpcodeStore);


  // Control logic: determine input to ALU based on bypassing for mx and wx cases
  // "raw" since these get updated later in case of sra, sll, and srl, since they modify alu input
  logic [31:0] x_alu_input1_fin_raw;
  logic [31:0] x_alu_input2_fin_raw;
  logic [31:0] x_store_data_fin;

  wire MX1_bypass; 
  wire MX2_bypass; 

  wire WX1_bypass; // only use is MX bypass isn't available
  wire WX2_bypass;

  // don't do anything to store_data in this stage, so this is just preparation for the next stage
  wire MX_store_data_bypass;
  wire WX_store_data_bypass;
  
  

  wire [1:0] x_s1_bypass_select; // bit 1: MX1 active. bit 0: WX1 active
  wire [1:0] x_s2_bypass_select;
  wire [1:0] x_store_data_bypass_select;

  // Don't try to bypass if rs1 is x0.
  // MX bypassing should already resolve load->store addr case (w/ stall)? Can modify if it does not
  assign MX1_bypass = ((memory_state.m_alu_result_adr == execute_state.x_alu_input1_adr) && execute_state.x_alu_input1_adr != 0);
  assign MX2_bypass = ((memory_state.m_alu_result_adr == execute_state.x_alu_input2_adr) && execute_state.x_alu_input2_adr != 0);

  assign WX1_bypass = (((writeback_state.w_alu_result_adr == execute_state.x_alu_input1_adr) && execute_state.x_alu_input1_adr != 0) || div_use1);
  assign WX2_bypass = (((writeback_state.w_alu_result_adr == execute_state.x_alu_input2_adr) && execute_state.x_alu_input2_adr != 0) || div_use2);

  assign MX_store_data_bypass = ((memory_state.m_alu_result_adr == execute_state.x_store_data_rf_adr) && execute_state.x_store_data_rf_adr != 0);
  assign WX_store_data_bypass = (((writeback_state.w_alu_result_adr == execute_state.x_store_data_rf_adr) && execute_state.x_store_data_rf_adr != 0) || div_use2);
  
  assign x_s1_bypass_select = {MX1_bypass, WX1_bypass};
  assign x_s2_bypass_select = {MX2_bypass, WX2_bypass};
  assign x_store_data_bypass_select = {MX_store_data_bypass, WX_store_data_bypass};

  wire MX_stall; // case where store address depends on load immediately preceding it
  assign MX_stall = (x_insn_rs1 == m_insn_rd) && m_is_load_op && x_is_store_op;


  // MUX to choose x1 input based on bypass availability
  always_comb begin
    case (x_s1_bypass_select)
      2'b00: begin  // neither active
        x_alu_input1_fin_raw = execute_state.x_alu_input1;
      end

      2'b01: begin // wx active only
        x_alu_input1_fin_raw = insn_result; // writeback_state.w_alu_result
      end

      2'b10: begin // mx active only
        x_alu_input1_fin_raw = memory_state.m_alu_result;
      end

      2'b11: begin  // both active
        x_alu_input1_fin_raw = memory_state.m_alu_result;
      end
    endcase

    // MUX to choose x2 input based on bypass availability
    case (x_s2_bypass_select)
      2'b00: begin  // neither active
        x_alu_input2_fin_raw = execute_state.x_alu_input2;
      end

      2'b01: begin // wx active only
        x_alu_input2_fin_raw = insn_result;
      end

      2'b10: begin // mx active only
        x_alu_input2_fin_raw = memory_state.m_alu_result;
      end

      2'b11: begin  // both active
        x_alu_input2_fin_raw = memory_state.m_alu_result;
      end
    endcase

    case (x_store_data_bypass_select)
      2'b00: begin  // neither active
        x_store_data_fin = execute_state.x_store_data;
      end

      2'b01: begin // wx active only
        x_store_data_fin = insn_result;
      end

      2'b10: begin // mx active only
        x_store_data_fin = memory_state.m_alu_result;
      end

      2'b11: begin  // both active
        x_store_data_fin = memory_state.m_alu_result;
      end
    endcase
  end
  



  // ALU
  wire [31:0] add_result; // add (also used for sub)
  cla ALU_add(.a(x_alu_input1_fin), .b(x_alu_input2_fin), .cin(1'b0), .sum(add_result));

  wire [63:0] mul_result; // multiply (need 64 bits because 2^32 * 2^32 = 2^64)
  assign mul_result = x_alu_input1_fin * x_alu_input2_fin;

  wire [63:0] mul_result_ss;
  assign mul_result_ss = $signed(x_alu_input1_fin) * $signed(x_alu_input2_fin);

  wire lt_result; // signed less than comparison
  assign lt_result = $signed($signed(x_alu_input1_fin) < $signed(x_alu_input2_fin)) ? 1 : 0;

  wire ltu_result; // unsigned less than comparison
  assign ltu_result = $unsigned(x_alu_input1_fin < (x_alu_input2_fin)) ? 1 : 0;

  wire ge_result; // signed greater than or equals to comparison
  assign ge_result = $signed($signed(x_alu_input1_fin) >= $signed(x_alu_input2_fin));

  wire geu_result; // unsigned greater than or equals to comparison
  assign geu_result = x_alu_input1_fin >= x_alu_input2_fin;

  wire equals_result; // equals comparison
  assign equals_result = x_alu_input1_fin == x_alu_input2_fin;

  wire not_equals_result; // not equals comparison
  assign not_equals_result = x_alu_input1_fin != x_alu_input2_fin;

  wire [31:0] xor_result; // xor
  assign xor_result = x_alu_input1_fin ^ x_alu_input2_fin;

  wire [31:0] or_result; // or
  assign or_result = x_alu_input1_fin | x_alu_input2_fin;

  wire [31:0] and_result; // and
  assign and_result = x_alu_input1_fin & x_alu_input2_fin;

  wire [31:0] lshift_result; // left-shift
  assign lshift_result = x_alu_input1_fin << x_alu_input2_fin;

  wire [31:0] rshift_result; // right-shift
  assign rshift_result = x_alu_input1_fin >> x_alu_input2_fin;

  wire [31:0] sgn_rshift_result; // signed right-shift
  assign sgn_rshift_result = $signed(x_alu_input1_fin) >>> x_alu_input2_fin;

  logic [63:0] mulhsu_result;

  // DIV ALU, takes two cycles instead of one, send directly to writeback stage (skipping memory)
  wire [31:0] div_quotient; // div
  wire [31:0] div_remainder; // rem
  divider_unsigned_pipelined ALU_div(.clk(clk), .rst(rst), .i_dividend(x_alu_input1_fin), 
  .i_divisor(x_alu_input2_fin), .o_quotient(div_quotient), .o_remainder(div_remainder));




  // MUX to select ALU result, and branch_decide
  logic [31:0] alu_result;
  logic branch_decide; // whether to branch or not
  logic [31:0] x_alu_input1_fin; // true final result
  logic [31:0] x_alu_input2_fin;
  logic x_is_load;
  logic x_is_div;
  logic div_sign_bit;
  logic rem_sign_bit;
  always_comb begin
    case (x_insn_opcode)
      OpcodeLui: begin
        x_alu_input1_fin = x_alu_input1_fin_raw;
        x_alu_input2_fin = x_alu_input2_fin_raw;
        alu_result = lshift_result;
      end

      OpcodeAuipc: begin
        x_alu_input1_fin = x_alu_input1_fin_raw;
        x_alu_input2_fin = x_alu_input2_fin_raw;
        alu_result = add_result;
      end

      OpcodeRegImm: begin // instructions involving an immediate
        x_alu_input1_fin = x_alu_input1_fin_raw;
        x_alu_input2_fin = x_alu_input2_fin_raw;
        case (x_insn_funct3)
          3'b000: begin // addi
            alu_result = add_result;
          end

          3'b010: begin // slti
            alu_result = {31'b0, lt_result};
          end

          3'b011: begin // sltiu
            alu_result = {31'b0, ltu_result};
          end

          3'b100: begin // xori
            alu_result = xor_result;
          end

          3'b110: begin // ori
            alu_result = or_result;
          end

          3'b111: begin // andi
            alu_result = and_result;
          end

          3'b001: begin // slli
            alu_result = lshift_result;
          end

          3'b101: begin // srli and srai
            case (x_insn_funct7)
              7'b0000000: begin // srli
                alu_result = rshift_result;
              end
              7'b0100000: begin // srai
                alu_result = sgn_rshift_result;
              end

              default: begin
                alu_result = 0;
              end
            endcase
          end

          default: begin
            alu_result = 0;
          end

          
        endcase
      end

      OpcodeRegReg: begin // instructions involving 2 regs
        case (x_insn_funct3)
          3'b000: begin // add, sub and mul
            x_alu_input1_fin = x_alu_input1_fin_raw;
            case (x_insn_funct7)
              7'b0000000: begin // add
                x_alu_input2_fin = x_alu_input2_fin_raw;
                alu_result = add_result;
              end
              7'b0100000: begin // sub
                x_alu_input2_fin = (32'b11111111111111111111111111111111 ^ x_alu_input2_fin_raw) + 1;
                alu_result = add_result;
              end
              7'b0000001: begin // mul
                x_alu_input2_fin = x_alu_input2_fin_raw;
                alu_result = mul_result[31:0];
              end
              default: begin
                alu_result = 0;
              end
            endcase
          end

          3'b001: begin // sll and mulh
            
            case (x_insn_funct7)
              7'b0000000: begin // sll
                x_alu_input1_fin = x_alu_input1_fin_raw;
                x_alu_input2_fin = {27'b0, x_alu_input2_fin_raw[4:0]}; // need to truncate bits here for case of MX2 bypass
                alu_result = lshift_result;
              end
              7'b0000001: begin // mulh
                x_alu_input1_fin = x_alu_input1_fin_raw;
                x_alu_input2_fin = x_alu_input2_fin_raw;
                alu_result = $signed(mul_result_ss[63:32]);
                // alu_result = mul_result_ss;
              end
              default: begin
                alu_result = 0;
              end
            endcase
          end

          3'b010: begin // slt and mulhsu
            
            x_alu_input2_fin = x_alu_input2_fin_raw;
            
            case (x_insn_funct7)
              7'b0000000: begin // slt
                x_alu_input1_fin = x_alu_input1_fin_raw;
                alu_result = {31'b0, lt_result};
              end
              7'b0000001: begin // mulhsu    
                logic mulhsu_sign_bit;
                mulhsu_sign_bit = x_alu_input1_fin_raw[31];
                x_alu_input1_fin = (x_alu_input1_fin_raw[31] == 1'b1) ? ((32'b11111111111111111111111111111111 ^ x_alu_input1_fin_raw) + 1) : $unsigned(x_alu_input1_fin_raw);
                mulhsu_result = mulhsu_sign_bit == 1'b1 ? ((64'b1111111111111111111111111111111111111111111111111111111111111111 ^ mul_result) + 1) : mul_result;
                alu_result = mulhsu_result[63:32];
              end
              default: begin
                alu_result = 0;
              end
            endcase
          end

          3'b011: begin // sltu and mulhu
            x_alu_input1_fin = x_alu_input1_fin_raw;
            x_alu_input2_fin = x_alu_input2_fin_raw;
            case (x_insn_funct7)
              7'b0000000: begin // sltu
                alu_result = {31'b0, ltu_result};
              end
              7'b0000001: begin // mulhu
                alu_result = mul_result[63:32];
              end
              default: begin
                alu_result = 0;
              end
            endcase
          end

          3'b100: begin // xor and div
            x_alu_input1_fin = x_alu_input1_fin_raw;
            x_alu_input2_fin = x_alu_input2_fin_raw;
            case (x_insn_funct7)
              7'b0000000: begin // xor
                alu_result = xor_result;
              end
              // 7'b0000001: begin // div
              //   logic div_sign_bit;
              //   div_sign_bit = rs2_out == 0 ? 0 : execute_state.x_alu_input1[31] ^ execute_state.x_alu_input2[31]; // set 0 if div by 0
              //   div_alu_result = div_sign_bit == 1'b1 ? ((32'b11111111111111111111111111111111 ^ div_quotient) + 1) : div_quotient;
              // end
              7'b0000001: begin // div
                div_sign_bit = x_alu_input2_fin_raw == 0 ? 0 : x_alu_input1_fin_raw[31] ^ x_alu_input2_fin_raw[31]; // set 0 if div by 0
                x_alu_input1_fin = (x_alu_input1_fin_raw[31] == 1'b1) ? ((32'b11111111111111111111111111111111 ^ x_alu_input1_fin_raw) + 1) : $unsigned(x_alu_input1_fin_raw);
                x_alu_input2_fin = (x_alu_input2_fin_raw[31] == 1'b1) ? ((32'b11111111111111111111111111111111 ^ x_alu_input2_fin_raw) + 1) : $unsigned(x_alu_input2_fin_raw);
                x_is_div = 1;
              end
              default: begin
                alu_result = 0;
              end
            endcase
          end

          3'b101: begin // srl, sra, and divu
            case (x_insn_funct7)
              7'b0000000: begin // srl
                x_alu_input1_fin = x_alu_input1_fin_raw;
                x_alu_input2_fin = {27'b0, x_alu_input2_fin_raw[4:0]};
                alu_result = rshift_result;
              end
              7'b0000001: begin // divu
                x_alu_input1_fin = x_alu_input1_fin_raw;
                x_alu_input2_fin = x_alu_input2_fin_raw;
                x_is_div = 1;
                // div_alu_result = div_quotient;
              end
              7'b0100000: begin // sra
                x_alu_input1_fin = x_alu_input1_fin_raw;
                x_alu_input2_fin = {27'b0, x_alu_input2_fin_raw[4:0]};
                alu_result = sgn_rshift_result;
              end
              default: begin
                alu_result = 0;
              end
            endcase
          end

          3'b110: begin // or & rem
            x_alu_input1_fin = x_alu_input1_fin_raw;
            x_alu_input2_fin = x_alu_input2_fin_raw;
            case (x_insn_funct7)
              7'b0000000: begin // or
                alu_result = or_result;
              end
              // 7'b0000001: begin // rem
              //   logic rem_sign_bit;
              //   rem_sign_bit = execute_state.x_alu_input2 == 0 ? 0 : rs1_out[31];
              //   div_alu_result = rem_sign_bit == 1'b1 ? ((32'b11111111111111111111111111111111 ^ div_remainder) + 1) : div_remainder;
              // end
              7'b0000001: begin
                rem_sign_bit = x_alu_input2_fin_raw == 0 ? 0 : x_alu_input1_fin_raw[31];
                x_alu_input1_fin = (x_alu_input1_fin_raw[31] == 1'b1) ? ((32'b11111111111111111111111111111111 ^ x_alu_input1_fin_raw) + 1) : $unsigned(x_alu_input1_fin_raw);
                x_alu_input2_fin = (x_alu_input2_fin_raw[31] == 1'b1) ? ((32'b11111111111111111111111111111111 ^ x_alu_input2_fin_raw) + 1) : $unsigned(x_alu_input2_fin_raw);
                x_is_div = 1;
              end
              default: begin
                alu_result = 0;
              end
            endcase
          end

          3'b111: begin // and & remu
            x_alu_input1_fin = x_alu_input1_fin_raw;
            x_alu_input2_fin = x_alu_input2_fin_raw;
            case (x_insn_funct7)
              7'b0000000: begin // and
                alu_result = and_result;
              end
              // 7'b0000001: begin // remu
              //   div_alu_result = div_remainder;
              // end
              7'b0000001: begin
                x_is_div = 1;
              end
              default: begin
                alu_result = 0;
              end
            endcase
          end
        endcase
      end

      OpcodeBranch: begin
        x_alu_input1_fin = x_alu_input1_fin_raw;
        x_alu_input2_fin = x_alu_input2_fin_raw;
        alt_PC = decode_state.d_pc_last + imm_b_sext;
        case (x_insn_funct3)
          3'b000: begin // beq
            branch_decide = equals_result;
          end

          3'b001: begin // bne
            branch_decide = not_equals_result;
          end

          3'b100: begin // blt
            branch_decide = lt_result;
          end

          3'b101: begin // bge
            branch_decide = ge_result;
          end

          3'b110: begin // bltu
            branch_decide = ltu_result;
          end

          3'b111: begin // bgeu
            branch_decide = geu_result;
          end

          default: begin
            branch_decide = 0;
          end
        endcase
      end

      OpcodeJal: begin
        x_alu_input1_fin = x_alu_input1_fin_raw;
        x_alu_input2_fin = x_alu_input2_fin_raw;
        alu_result = execute_state.x_pc + 4; // rd = pc + 4, gets written to a register
        alt_PC = add_result;
        branch_decide = 1;
      end

      OpcodeJalr: begin
        x_alu_input1_fin = x_alu_input1_fin_raw;
        x_alu_input2_fin = x_alu_input2_fin_raw;
        alu_result = execute_state.x_pc + 4; // rd = pc + 4, gets written to a register
        alt_PC = add_result;
        branch_decide = 1;
      end

      OpcodeLoad: begin
        x_alu_input1_fin = x_alu_input1_fin_raw;
        x_alu_input2_fin = x_alu_input2_fin_raw;
        x_is_load = 1;
        alu_result = add_result;
      end

      OpcodeStore: begin
        x_alu_input1_fin = x_alu_input1_fin_raw;
        x_alu_input2_fin = x_alu_input2_fin_raw;
        alu_result = add_result;
      end

      default: begin
        x_is_load = 0;
        x_is_div = 0;
        x_alu_input1_fin = 0;
        x_alu_input2_fin = 0;
        alu_result = 0;
        branch_decide = 0;
        alt_PC = 0;
      end
    endcase
  end
  

  /****************/
  /* MEMORY STAGE */
  /****************/
  
  stage_memory_t memory_state;
  always_ff @(posedge clk) begin
    if (rst) begin
      memory_state <= '{
        m_pc: 0,
        m_insn: 0,
        m_alu_result: 0,
        m_rs2: 0,
        m_store_data: 0,
        m_alu_result_adr: 0,
        m_branch_decide: 0,
        m_branch_result: 0,
        m_div_sign_bit: 0,
        m_rem_sign_bit: 0,
        m_halt: 0,
        m_cycle_status: CYCLE_RESET
      };
    end else begin
      begin
        memory_state <= '{
          m_pc: MX_stall ? 0 : execute_state.x_pc,
          m_insn: MX_stall ? 0 : execute_state.x_insn,
          m_alu_result: MX_stall ? 0 : alu_result,
          m_rs2: MX_stall ? 0 : execute_state.x_alu_input2,
          // m_store_data: MX_stall ? 0 : (WX_data_bypass ? writeback_state.w_mem_result : execute_state.x_store_data),
          m_store_data: MX_stall ? 0 : x_store_data_fin,
          m_alu_result_adr: MX_stall ? 0 : execute_state.x_alu_result_adr,
          m_branch_decide:  MX_stall ? 0 : branch_decide, 
          m_branch_result: MX_stall ? 0 : alt_PC,
          m_halt: MX_stall ? 0 : execute_state.x_halt,
          m_div_sign_bit: MX_stall ? 0 : div_sign_bit,
          m_rem_sign_bit: MX_stall ? 0 : rem_sign_bit,
          m_cycle_status: execute_state.x_cycle_status
        };
      end
    end
  end

  Disasm #(
      .PREFIX("M")
  ) disasm_3memory (
      .insn  (memory_state.m_insn),
      .disasm()
  );

  

  // get information from instruction
  wire [6:0] m_insn_funct7;
  wire [4:0] m_insn_rs2; // address of stored data value
  wire [4:0] m_insn_rs1; // not used in this stage
  wire [2:0] m_insn_funct3;
  wire [4:0] m_insn_rd;
  wire [6:0] m_insn_opcode;

  // split R-type instruction - see section 2.2 of RiscV spec
  assign {m_insn_funct7, m_insn_rs2, m_insn_rs1, m_insn_funct3, m_insn_rd, m_insn_opcode} = memory_state.m_insn;

  wire m_is_load_op;
  assign m_is_load_op = (m_insn_opcode == OpcodeLoad);
  
  wire m_is_store_op;
  assign m_is_store_op = (m_insn_opcode == OpcodeStore);

  wire m_is_nop;
  assign m_is_nop = (memory_state.m_insn == 0);

  // determine which part of the chunk gets accessed
  wire [1:0] offset_parity;
  assign offset_parity = memory_state.m_alu_result[1:0]; // junk value if not load instruction

  wire WM_data_bypass;
  assign WM_data_bypass = (m_insn_rs2 == w_insn_rd) && w_is_load_op && m_is_store_op;

  // wire WX_data_bypass;
  // assign WX_data_bypass = (x_insn_rs2 == w_insn_rd) && w_is_load_op && m_is_nop && x_is_store_op;


  // select final data value to get stored into memory based on bypassing availability
  wire [31:0] store_data_fin;
  assign store_data_fin = WM_data_bypass ? writeback_state.w_mem_result : memory_state.m_store_data;
  
  logic [31:0] mem_result;
  // mux for determining what address to send to mem, and what to get back
  always_comb begin
    case (m_insn_opcode) // unique for opcodeload and opcodestore, all else is covered by default
      OpcodeLoad: begin
        store_we_to_dmem = 0;
        addr_to_dmem = {memory_state.m_alu_result[31:2], 2'b0};
        case (m_insn_funct3)
          3'b000: begin // lb (s-ext)
            case (offset_parity)
              2'b00: begin // 4-indexed
                mem_result = {{24{load_data_from_dmem[7]}}, load_data_from_dmem[7:0]};
              end

              2'b01: begin // 1-indexed
                mem_result = {{24{load_data_from_dmem[15]}}, load_data_from_dmem[15:8]};
              end

              2'b10: begin // 2-indexed
                mem_result = {{24{load_data_from_dmem[23]}}, load_data_from_dmem[23:16]};
              end

              2'b11: begin // 3-indexed
                mem_result = {{24{load_data_from_dmem[31]}}, load_data_from_dmem[31:24]};
              end           
            endcase         
          end

          3'b001: begin // lh (s-ext)
            case (offset_parity)
              2'b00: begin
                mem_result = {{16{load_data_from_dmem[15]}}, load_data_from_dmem[15:0]};
              end

              2'b10: begin
                mem_result = {{16{load_data_from_dmem[31]}}, load_data_from_dmem[31:16]};
              end

              default: begin // somehow still misaligned
                mem_result = 32'b0; 
              end
            endcase
          end

          3'b010: begin // lw
            mem_result = load_data_from_dmem;
          end

          3'b100: begin // lbu (zero-ext)
            case (offset_parity)
              2'b00: begin // 4-indexed
                mem_result = {{24'b0}, load_data_from_dmem[7:0]};
              end

              2'b01: begin // 1-indexed
                mem_result = {{24'b0}, load_data_from_dmem[15:8]};
              end

              2'b10: begin // 2-indexed
                mem_result = {{24'b0}, load_data_from_dmem[23:16]};
              end

              2'b11: begin // 3-indexed
                mem_result = {{24'b0}, load_data_from_dmem[31:24]};
              end           
            endcase
          end

          3'b101: begin // lhu (zero-ext)
            case (offset_parity)
              2'b00: begin
                mem_result = {{16'b0}, load_data_from_dmem[15:0]};
              end

              2'b10: begin
                mem_result = {{16'b0}, load_data_from_dmem[31:16]};
              end

              default: begin // somehow still misaligned
                mem_result = 32'b0; 
              end
            endcase
          end

          default: begin
            mem_result = 32'b0;
          end
        endcase
      end

      OpcodeStore: begin
        addr_to_dmem = {memory_state.m_alu_result[31:2], 2'b0};
        mem_result = 0;
        case (m_insn_funct3)
          3'b000: begin // sb
            case (offset_parity) // apply mask based on the offset
              2'b00: begin // 4-indexed
                // store_data_to_dmem = {{24'b0}, rs2_out[7:0]};
                store_data_to_dmem = {{24'b0}, store_data_fin[7:0]};
                store_we_to_dmem = 4'b0001;
              end

              2'b01: begin // 1-indexed
                // store_data_to_dmem = {{24'b0}, rs2_out[15:8]};
                store_data_to_dmem = {{16'b0}, store_data_fin[7:0], {8'b0}};
                store_we_to_dmem = 4'b0010;
              end

              2'b10: begin // 2-indexed
                // store_data_to_dmem = {{24'b0}, rs2_out[23:16]};
                store_data_to_dmem = {{8'b0}, store_data_fin[7:0], {16'b0}};
                store_we_to_dmem = 4'b0100;
              end

              2'b11: begin // 3-indexed
                // store_data_to_dmem = {{24'b0}, rs2_out[31:24]};
                store_data_to_dmem = {store_data_fin[7:0], {24'b0}};
                store_we_to_dmem = 4'b1000;
              end
            endcase
          end

          3'b001: begin // sh
            case (offset_parity)
              2'b00: begin
                // store_data_to_dmem = {{16'b0}, rs2_out[15:0]};
                store_data_to_dmem = {{16'b0}, store_data_fin[15:0]};
                store_we_to_dmem = 4'b0011;
              end

              2'b10: begin
                // store_data_to_dmem = {{16'b0}, rs2_out[31:16]};
                store_data_to_dmem = {store_data_fin[15:0], {16'b0}};
                store_we_to_dmem = 4'b1100;
              end

              default: begin // somehow still misaligned
                // store_data_to_dmem = 32'b0; 
                store_data_to_dmem = 0;
                store_we_to_dmem = 4'b0000;
              end
            endcase
          end

          3'b010: begin  // sw 
            store_data_to_dmem = store_data_fin;
            store_we_to_dmem = 4'b1111;
          end 

          default: begin
            store_data_to_dmem = 0;
            store_we_to_dmem = 0;
          end
        endcase
      end

      default: begin
        store_we_to_dmem = 0;
        addr_to_dmem = 0;
        mem_result = 0;
      end
    endcase
  end

  // div ALU
  logic [31:0] div_alu_result;
  always_comb begin
    case (m_insn_opcode)
      OpcodeRegReg: begin
        case (m_insn_funct7)
          7'b0000001: begin
            case (m_insn_funct3)
              3'b100: begin // div
                div_alu_result = memory_state.m_div_sign_bit == 1'b1 ? ((32'b11111111111111111111111111111111 ^ div_quotient) + 1) : div_quotient;
              end

              3'b101: begin // divu
                div_alu_result = div_quotient;
              end

              3'b110: begin // rem
                div_alu_result = memory_state.m_rem_sign_bit == 1'b1 ? ((32'b11111111111111111111111111111111 ^ div_remainder) + 1) : div_remainder;
              end

              3'b111: begin // remu
                div_alu_result = div_remainder;
              end
              default: begin
                div_alu_result = 0;
              end
            endcase
          end
          default: begin
            div_alu_result = 0;
          end
        endcase
      end

      default: begin
        div_alu_result = 0;
      end
    endcase
  end

  /*******************/
  /* WRITEBACK STAGE */
  /*******************/
  
  stage_writeback_t writeback_state;
  always_ff @(posedge clk) begin
    if (rst) begin
      writeback_state <= '{
        w_pc: 0,
        w_insn: 0,
        w_alu_result: 0,
        w_div_alu_result: 0,
        w_alu_result_adr: 0,
        w_mem_result: 0,
        w_halt: 0,
        w_cycle_status: CYCLE_RESET
      };
    end else begin
      begin
        writeback_state <= '{
          w_pc: memory_state.m_pc,
          w_insn: memory_state.m_insn,
          w_alu_result: memory_state.m_alu_result,
          w_div_alu_result: div_alu_result,
          w_alu_result_adr: memory_state.m_alu_result_adr,
          w_mem_result: mem_result,
          w_halt: memory_state.m_halt,
          w_cycle_status: memory_state.m_cycle_status
        };
      end
    end
  end

  Disasm #(
      .PREFIX("W")
  ) disasm_4writeback (
      .insn  (writeback_state.w_insn),
      .disasm()
  );

  // Take opcode from insn:
  // decode all the information from the instruction assuming R-type
  wire [6:0] w_insn_funct7;
  wire [4:0] w_insn_rs2;
  wire [4:0] w_insn_rs1;
  wire [2:0] w_insn_funct3;
  wire [4:0] w_insn_rd;
  wire [6:0] w_insn_opcode;

  // split R-type instruction - see section 2.2 of RiscV spec
  assign {w_insn_funct7, w_insn_rs2, w_insn_rs1, w_insn_funct3, w_insn_rd, w_insn_opcode} = writeback_state.w_insn;

  wire is_mem_op;
  assign is_mem_op = ((w_insn_opcode == OpcodeStore) || (w_insn_opcode == OpcodeLoad));

  wire w_is_load_op;
  assign w_is_load_op = (w_insn_opcode == OpcodeLoad);

  wire is_div_op;
  assign is_div_op = (((w_insn_opcode == OpcodeRegReg) && w_insn_funct7 == 7'b1) && (w_insn_funct3 == 3'b100 || w_insn_funct3 == 3'b101 || w_insn_funct3 == 3'b110 || w_insn_funct3 == 3'b111));

  // MUX to choose between memory result and alu result before writing back
  wire [31:0] insn_result; 
  assign insn_result = is_mem_op ? writeback_state.w_mem_result : (is_div_op ? writeback_state.w_div_alu_result : writeback_state.w_alu_result);


  wire we_sig; // write-enable
  assign we_sig = ((w_insn_opcode != OpcodeBranch) & (w_insn_opcode != OpcodeStore));

  // halt pc if signal is active
  assign halt = writeback_state.w_halt;

  assign trace_writeback_insn = writeback_state.w_insn;
  assign trace_writeback_pc = writeback_state.w_pc;
  assign trace_writeback_cycle_status = writeback_state.w_cycle_status;

endmodule



module MemorySingleCycle #(
    parameter int NUM_WORDS = 512
) (
    // rst for both imem and dmem
    input wire rst,

    // clock for both imem and dmem. The memory reads/writes on @(negedge clk)
    input wire clk,

    // must always be aligned to a 4B boundary
    input wire [`REG_SIZE] pc_to_imem,

    // the value at memory location pc_to_imem
    output logic [`REG_SIZE] insn_from_imem,

    // must always be aligned to a 4B boundary
    input wire [`REG_SIZE] addr_to_dmem,

    // the value at memory location addr_to_dmem
    output logic [`REG_SIZE] load_data_from_dmem,

    // the value to be written to addr_to_dmem, controlled by store_we_to_dmem
    input wire [`REG_SIZE] store_data_to_dmem,

    // Each bit determines whether to write the corresponding byte of store_data_to_dmem to memory location addr_to_dmem.
    // E.g., 4'b1111 will write 4 bytes. 4'b0001 will write only the least-significant byte.
    input wire [3:0] store_we_to_dmem
);

  /* verilator lint_off VARHIDDEN */
  // memory is arranged as an array of 4B words
  logic [`REG_SIZE] mem[NUM_WORDS];

  initial begin
    $readmemh("mem_initial_contents.hex", mem, 0);
  end

  always_comb begin
    // memory addresses should always be 4B-aligned
    assert (pc_to_imem[1:0] == 2'b00);
    assert (addr_to_dmem[1:0] == 2'b00);
  end

  localparam int AddrMsb = $clog2(NUM_WORDS) + 1;
  localparam int AddrLsb = 2;

  always @(negedge clk) begin
    if (rst) begin
    end else begin
      insn_from_imem <= mem[{pc_to_imem[AddrMsb:AddrLsb]}];
    end
  end

  always @(negedge clk) begin
    if (rst) begin
    end else begin
      if (store_we_to_dmem[0]) begin
        mem[addr_to_dmem[AddrMsb:AddrLsb]][7:0] <= store_data_to_dmem[7:0];
      end
      if (store_we_to_dmem[1]) begin
        mem[addr_to_dmem[AddrMsb:AddrLsb]][15:8] <= store_data_to_dmem[15:8];
      end
      if (store_we_to_dmem[2]) begin
        mem[addr_to_dmem[AddrMsb:AddrLsb]][23:16] <= store_data_to_dmem[23:16];
      end
      if (store_we_to_dmem[3]) begin
        mem[addr_to_dmem[AddrMsb:AddrLsb]][31:24] <= store_data_to_dmem[31:24];
      end
      // dmem is "read-first": read returns value before the write
      load_data_from_dmem <= mem[{addr_to_dmem[AddrMsb:AddrLsb]}];
    end
  end
endmodule

/* This design has just one clock for both processor and memory. */
module RiscvProcessor (
    input  wire  clk,
    input  wire  rst,
    output logic halt,
    output wire [`REG_SIZE] trace_writeback_pc,
    output wire [`INSN_SIZE] trace_writeback_insn,
    output cycle_status_e trace_writeback_cycle_status
);

  wire [`INSN_SIZE] insn_from_imem;
  wire [`REG_SIZE] pc_to_imem, mem_data_addr, mem_data_loaded_value, mem_data_to_write;
  wire [3:0] mem_data_we;

  MemorySingleCycle #(
      .NUM_WORDS(8192)
  ) the_mem (
      .rst                (rst),
      .clk                (clk),
      // imem is read-only
      .pc_to_imem         (pc_to_imem),
      .insn_from_imem     (insn_from_imem),
      // dmem is read-write
      .addr_to_dmem       (mem_data_addr),
      .load_data_from_dmem(mem_data_loaded_value),
      .store_data_to_dmem (mem_data_to_write),
      .store_we_to_dmem   (mem_data_we)
  );

  /* verilator lint_off VARHIDDEN */

  DatapathPipelined datapath (
      .clk(clk),
      .rst(rst),
      .pc_to_imem(pc_to_imem),
      .insn_from_imem(insn_from_imem),
      .addr_to_dmem(mem_data_addr),
      .store_data_to_dmem(mem_data_to_write),
      .store_we_to_dmem(mem_data_we),
      .load_data_from_dmem(mem_data_loaded_value),
      .halt(halt),
      .trace_writeback_pc(trace_writeback_pc),
      .trace_writeback_insn(trace_writeback_insn),
      .trace_writeback_cycle_status(trace_writeback_cycle_status)
  );

endmodule

