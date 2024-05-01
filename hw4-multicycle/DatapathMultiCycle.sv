/* INSERT NAME AND PENNKEY HERE */

`timescale 1ns / 1ns

// registers are 32 bits in RV32
`define REG_SIZE 31:0

// RV opcodes are 7 bits
`define OPCODE_SIZE 6:0

`ifndef RISCV_FORMAL
`include "../hw2b/cla.sv"
`include "divider_unsigned_pipelined.sv"
`include "../hw3-singlecycle/RvDisassembler.sv"
`endif

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

  // TODO: copy your HW3B code here
  localparam int NumRegs = 32;
  logic [`REG_SIZE] regs[NumRegs];

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

module DatapathMultiCycle (
    input wire clk,
    input wire rst,
    output logic halt,
    output logic [`REG_SIZE] pc_to_imem,
    input wire [`REG_SIZE] insn_from_imem,
    // addr_to_dmem is a read-write port
    output logic [`REG_SIZE] addr_to_dmem,
    input wire [`REG_SIZE] load_data_from_dmem,
    output logic [`REG_SIZE] store_data_to_dmem,
    output logic [3:0] store_we_to_dmem
);

  // TODO: your code here (largely based on HW3B)
  // components of the instruction
  wire [6:0] insn_funct7;
  wire [4:0] insn_rs2;
  wire [4:0] insn_rs1;
  wire [2:0] insn_funct3;
  wire [4:0] insn_rd;
  wire [`OPCODE_SIZE] insn_opcode;

  // split R-type instruction - see section 2.2 of RiscV spec
  assign {insn_funct7, insn_rs2, insn_rs1, insn_funct3, insn_rd, insn_opcode} = insn_from_imem;

  // U
  wire [19:0] imm_u;
  assign imm_u = insn_from_imem[31:12];

  // setup for I, S, B & J type instructions
  // I - short immediates and loads
  wire [11:0] imm_i;
  assign imm_i = insn_from_imem[31:20];
  wire [ 4:0] imm_shamt = insn_from_imem[24:20];

  // S - stores
  wire [11:0] imm_s;
  assign imm_s[11:5] = insn_funct7, imm_s[4:0] = insn_rd;

  // B - conditionals
  wire [12:0] imm_b;
  assign {imm_b[12], imm_b[10:5]} = insn_funct7, {imm_b[4:1], imm_b[11]} = insn_rd, imm_b[0] = 1'b0;

  // J - unconditional jumps
  wire [20:0] imm_j;
  assign {imm_j[20], imm_j[10:1], imm_j[11], imm_j[19:12], imm_j[0]} = {insn_from_imem[31:12], 1'b0};

  wire [`REG_SIZE] imm_i_sext = {{20{imm_i[11]}}, imm_i[11:0]};
  wire [`REG_SIZE] imm_s_sext = {{20{imm_s[11]}}, imm_s[11:0]};
  wire [`REG_SIZE] imm_b_sext = {{19{imm_b[12]}}, imm_b[12:0]};
  wire [`REG_SIZE] imm_j_sext = {{11{imm_j[20]}}, imm_j[20:0]};
  wire [`REG_SIZE] imm_u_sext = {{12{imm_u[19]}}, imm_u[19:0]};

  // opcodes - see section 19 of RiscV spec
  localparam bit [`OPCODE_SIZE] OpLoad = 7'b00_000_11;
  localparam bit [`OPCODE_SIZE] OpStore = 7'b01_000_11;
  localparam bit [`OPCODE_SIZE] OpBranch = 7'b11_000_11;
  localparam bit [`OPCODE_SIZE] OpJalr = 7'b11_001_11;
  localparam bit [`OPCODE_SIZE] OpMiscMem = 7'b00_011_11;
  localparam bit [`OPCODE_SIZE] OpJal = 7'b11_011_11;

  localparam bit [`OPCODE_SIZE] OpRegImm = 7'b00_100_11;
  localparam bit [`OPCODE_SIZE] OpRegReg = 7'b01_100_11;
  localparam bit [`OPCODE_SIZE] OpEnviron = 7'b11_100_11;

  localparam bit [`OPCODE_SIZE] OpAuipc = 7'b00_101_11;
  localparam bit [`OPCODE_SIZE] OpLui = 7'b01_101_11;

  wire insn_lui = insn_opcode == OpLui;
  wire insn_auipc = insn_opcode == OpAuipc;
  wire insn_jal = insn_opcode == OpJal;
  wire insn_jalr = insn_opcode == OpJalr;

  wire insn_beq = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b000;
  wire insn_bne = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b001;
  wire insn_blt = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b100;
  wire insn_bge = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b101;
  wire insn_bltu = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b110;
  wire insn_bgeu = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b111;

  wire insn_lb = insn_opcode == OpLoad && insn_from_imem[14:12] == 3'b000;
  wire insn_lh = insn_opcode == OpLoad && insn_from_imem[14:12] == 3'b001;
  wire insn_lw = insn_opcode == OpLoad && insn_from_imem[14:12] == 3'b010;
  wire insn_lbu = insn_opcode == OpLoad && insn_from_imem[14:12] == 3'b100;
  wire insn_lhu = insn_opcode == OpLoad && insn_from_imem[14:12] == 3'b101;

  wire insn_sb = insn_opcode == OpStore && insn_from_imem[14:12] == 3'b000;
  wire insn_sh = insn_opcode == OpStore && insn_from_imem[14:12] == 3'b001;
  wire insn_sw = insn_opcode == OpStore && insn_from_imem[14:12] == 3'b010;

  wire insn_addi = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b000;
  wire insn_slti = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b010;
  wire insn_sltiu = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b011;
  wire insn_xori = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b100;
  wire insn_ori = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b110;
  wire insn_andi = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b111;

  wire insn_slli = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b001 && insn_from_imem[31:25] == 7'd0;
  wire insn_srli = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b101 && insn_from_imem[31:25] == 7'd0;
  wire insn_srai = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b101 && insn_from_imem[31:25] == 7'b0100000;

  wire insn_add = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b000 && insn_from_imem[31:25] == 7'd0;
  wire insn_sub  = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b000 && insn_from_imem[31:25] == 7'b0100000;
  wire insn_sll = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b001 && insn_from_imem[31:25] == 7'd0;
  wire insn_slt = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b010 && insn_from_imem[31:25] == 7'd0;
  wire insn_sltu = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b011 && insn_from_imem[31:25] == 7'd0;
  wire insn_xor = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b100 && insn_from_imem[31:25] == 7'd0;
  wire insn_srl = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b101 && insn_from_imem[31:25] == 7'd0;
  wire insn_sra  = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b101 && insn_from_imem[31:25] == 7'b0100000;
  wire insn_or = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b110 && insn_from_imem[31:25] == 7'd0;
  wire insn_and = insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b111 && insn_from_imem[31:25] == 7'd0;

  wire insn_mul    = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b000;
  wire insn_mulh   = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b001;
  wire insn_mulhsu = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b010;
  wire insn_mulhu  = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b011;
  wire insn_div    = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b100;
  wire insn_divu   = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b101;
  wire insn_rem    = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b110;
  wire insn_remu   = insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1 && insn_from_imem[14:12] == 3'b111;

  wire insn_ecall = insn_opcode == OpEnviron && insn_from_imem[31:7] == 25'd0;
  wire insn_fence = insn_opcode == OpMiscMem;

  // synthesis translate_off
  // this code is only for simulation, not synthesis
  // `include "RvDisassembler.sv"
  string disasm_string;
  always_comb begin
    disasm_string = rv_disasm(insn_from_imem);
  end
  // HACK: get disasm_string to appear in GtkWave, which can apparently show only wire/logic...
  wire [(8*32)-1:0] disasm_wire;
  genvar i;
  for (i = 0; i < 32; i = i + 1) begin : gen_disasm
    assign disasm_wire[(((i+1))*8)-1:((i)*8)] = disasm_string[31-i];
  end
  // synthesis translate_on

  // program counter
  logic [`REG_SIZE] pcNext, pcCurrent;
  always @(posedge clk) begin
    if (rst) begin
      pcCurrent <= 32'd0;
    end else begin
      pcCurrent <= pcNext;
    end
  end
  assign pc_to_imem = pcCurrent;

  // unconditional increment by 4, for case with no branch. Except for when there is a divide, then stall first
  
  wire [31:0] pc_unc_inc;
  assign pc_unc_inc = pc_to_imem + 32'b100;

  // cycle/insn_from_imem counters
  logic [`REG_SIZE] cycles_current, num_insns_current;
  always @(posedge clk) begin
    if (rst) begin
      cycles_current <= 0;
      num_insns_current <= 0;
    end else begin
      cycles_current <= cycles_current + 1;
      if (!rst) begin
        num_insns_current <= num_insns_current + 1;
      end
    end
  end

    // components of the instruction
  // wire [6:0] insn_funct7;
  // wire [4:0] insn_rs2;
  // wire [4:0] insn_rs1;
  // wire [2:0] insn_funct3;
  // wire [4:0] insn_rd;
  // wire [`OPCODE_SIZE] insn_opcode;

  wire not_branch;
  assign not_branch = insn_opcode != OpBranch;

  wire not_store;
  assign not_store = insn_opcode != OpStore;

  wire we_sig; // write-enable
  assign we_sig = not_branch & not_store;

  // Reg file
  wire [31:0] rs1_out;
  wire [31:0] rs2_out;
  RegFile rf(.rd(insn_rd),
    .rd_data(insn_result), // 32b input signal
    .rs1(insn_rs1),
    .rs1_data(rs1_out), // 32b output signal
    .rs2(insn_rs2),
    .rs2_data(rs2_out), // 32b output signal

    .clk(clk),
    .we(we_sig),
    .rst(rst));

  // ALU
  wire [31:0] add_result; // add (also used for sub)
  cla ALU_add(.a(ALU_input1), .b(ALU_input2), .cin(1'b0), .sum(add_result));

  wire [31:0] div_quotient; // div
  wire [31:0] div_remainder; // rem
  divider_unsigned_pipelined ALU_div(.clk(clk), .rst(rst), .i_dividend(ALU_input1), .i_divisor(ALU_input2), .o_quotient(div_quotient), .o_remainder(div_remainder));


  wire [63:0] mul_result; // multiply (need 64 bits because 2^32 * 2^32 = 2^64)
  assign mul_result = ALU_input1 * ALU_input2;

  // wire [63:0] mul_result_su;
  // assign mul_result_su = $signed($signed(ALU_input1) * ALU_input2);
  // assign mul_result_su = $signed(ALU_input1) * $unsigned(ALU_input2);

  wire [63:0] mul_result_ss;
  // assign mul_result_su = $signed($signed(ALU_input1) * $signed(ALU_input2));
  assign mul_result_ss = $signed(ALU_input1) * $signed(ALU_input2);



  wire lt_result; // signed less than comparison
  assign lt_result = $signed($signed(ALU_input1) < $signed(ALU_input2)) ? 1 : 0;
  // assign lt_result = ALU_input1 < $signed(ALU_input2);

  wire ltu_result; // unsigned less than comparison
  assign ltu_result = $unsigned(ALU_input1 < (ALU_input2)) ? 1 : 0;

  wire [31:0] xor_result; // xor
  assign xor_result = ALU_input1 ^ ALU_input2;

  wire [31:0] or_result; // or
  assign or_result = ALU_input1 | ALU_input2;

  wire [31:0] and_result; // and
  assign and_result = ALU_input1 & ALU_input2;

  wire [31:0] lshift_result; // left-shift
  assign lshift_result = ALU_input1 << ALU_input2;

  wire [31:0] rshift_result; // right-shift
  assign rshift_result = ALU_input1 >> ALU_input2;

  wire [31:0] sgn_rshift_result; // signed right-shift
  assign sgn_rshift_result = $signed(ALU_input1) >>> ALU_input2;

  logic [63:0] mulhsu_result;

  always_comb begin
    case (insn_opcode)
      OpAuipc: begin
        alu_result = add_result;
      end

      OpRegImm: begin // instructions involving an immediate
        case (insn_funct3)
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
            case (insn_funct7)
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

      OpRegReg: begin // instructions involving 2 regs
        case (insn_funct3)
          3'b000: begin // add, sub and mul
            case (insn_funct7)
              7'b0000000: begin // add
                alu_result = add_result;
              end
              7'b0100000: begin // sub
                alu_result = add_result;
              end
              7'b0000001: begin // mul
                alu_result = mul_result[31:0];
              end
              default: begin
                alu_result = 0;
              end
            endcase
          end

          3'b001: begin // sll and mulh
            
            case (insn_funct7)
              7'b0000000: begin // sll
                alu_result = lshift_result;
              end
              7'b0000001: begin // mulh
                alu_result = $signed(mul_result_ss[63:32]);
                // alu_result = mul_result_ss;
              end
              default: begin
                alu_result = 0;
              end
            endcase
          end

          3'b010: begin // slt and mulhsu
            case (insn_funct7)
              7'b0000000: begin // slt
                alu_result = {31'b0, lt_result};
              end
              7'b0000001: begin // mulhsu
                // alu_result = $signed(mul_result_su[63:32]);
                // alu_result = mul_su_sext[63:32];
                // alu_result = ALU_input2[31] == 1 ? (32'b11111111111111111111111111111111 ^ mul_result_su[63:32]) + 1;
                // alu_result = mul_result_su;

                mulhsu_result = mulhsu_sign_bit == 1'b1 ? ((64'b1111111111111111111111111111111111111111111111111111111111111111 ^ mul_result) + 1) : mul_result;

                alu_result = mulhsu_result[63:32];

              end
              default: begin
                alu_result = 0;
              end
            endcase
          end

          3'b011: begin // sltu and mulhu
            case (insn_funct7)
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
            case (insn_funct7)
              7'b0000000: begin // xor
                alu_result = xor_result;
              end
              7'b0000001: begin // div

                alu_result = div_sign_bit == 1'b1 ? ((32'b11111111111111111111111111111111 ^ div_quotient) + 1) : div_quotient;
              end
              default: begin
                alu_result = 0;
              end
            endcase
          end

          3'b101: begin // srl, sra, and divu
            case (insn_funct7)
              7'b0000000: begin // srl
                alu_result = rshift_result;
              end
              7'b0000001: begin // divu
                alu_result = div_quotient;
              end
              7'b0100000: begin // sra
                alu_result = sgn_rshift_result;
              end
              default: begin
                alu_result = 0;
              end
            endcase
          end

          3'b110: begin // or & rem
            case (insn_funct7)
              7'b0000000: begin // or
                alu_result = or_result;
              end
              7'b0000001: begin // rem
                alu_result = rem_sign_bit == 1'b1 ? ((32'b11111111111111111111111111111111 ^ div_remainder) + 1) : div_remainder;
              end
              default: begin
                alu_result = 0;
              end
            endcase
          end

          3'b111: begin // and & remu
            case (insn_funct7)
              7'b0000000: begin // and
                alu_result = and_result;
              end
              7'b0000001: begin // remu
                alu_result = div_remainder;
              end
              default: begin
                alu_result = 0;
              end
            endcase
          end
        endcase
      end

      OpJal: begin
        alu_result = add_result;
      end

      OpJalr: begin
        alu_result = {add_result[31:1], 1'b0}; // last bit needs to be 0
      end

      OpLoad: begin
        case (insn_funct3) // index address based on load type
          3'b000: begin // lb (s-ext)
            alu_result = {add_result[31:2], 2'b0};
            offset_parity = add_result[1:0];
          end

          3'b001: begin // lh (s-ext)
            alu_result = {add_result[31:2], 2'b0};
            offset_parity = add_result[1:0];

          end

          3'b010: begin // lw
            alu_result = add_result;
          end

          3'b100: begin // lbu (zero-ext)
            alu_result = {add_result[31:2], 2'b0};
            offset_parity = add_result[1:0];
          end

          3'b101: begin // lhu (zero-ext)
            alu_result = {add_result[31:2], 2'b0};
            offset_parity = add_result[1:0];
          end

          default: begin
            alu_result = 32'b0;
            offset_parity = 2'b0;
          end
        endcase
      end

      OpStore: begin
        alu_result = {add_result[31:2], 2'b0};
        offset_parity = add_result[1:0];
        // case (insn_funct3)
        //   3'b000: begin // sb
        //     alu_result = {add_result[31:2], 2'b0};
        //     offset_parity = add_result[1:0];
        //   end

        //   3'b001: begin // sh
        //     alu_result = {add_result[31:2], 2'b0};
        //     offset_parity = add_result[1:0];
        //   end

        //   3'b010: begin  // sw 
        //     alu_result = add_result;
        //   end 

        //   default: begin
        //     alu_result = 0;
        //   end
        // endcase
      end

      OpMiscMem: begin
        alu_result = 0;
      end

      default: begin
        alu_result = 0;
      end 
    endcase
  end
  


  logic illegal_insn;
  logic [31:0] lui_result; 
  logic [31:0] alu_result;
  logic [31:0] insn_result; // eventual feed back into register file
  logic [31:0] ALU_input1;
  logic [31:0] ALU_input2;
  logic [31:0] extended_rs2;


  logic [31:0] branch_ALU_input1; // branch inputs
  logic [31:0] branch_ALU_input2;
  logic [31:0] target_branch; // pc displacement
  logic [31:0] alt_PC; // alt_PC = PC + target_branch

  logic [31:0] test_sign1;
  logic [31:0] test_sign2;
  logic test_sign_result;

  logic mulhsu_sign_bit; // figure out ahead of time to get sign right for mulhsu op
  logic div_sign_bit;
  logic rem_sign_bit;

  logic [1:0] offset_parity; // determine if offset is multiple of 1, 2, 3, or 4 (incl 0)

  logic divide_state; // counter to check progress of divide instruction, used to prevent program 
  // counter from incrementing if still in first stage

  // divide state register
  always_ff @(posedge clk) begin
    if (rst) begin
      divide_state <= 1'd0;
    end else begin
      if (insn_div || insn_divu || insn_rem || insn_remu) begin
        if (divide_state == 0) begin
          divide_state <= 1;
        end

        if (divide_state == 1) begin
          divide_state <= 0;
        end
      end
    end
  end
  
  // instruction decode
  always_comb begin
    halt = 0;
    illegal_insn = 1'b0;
    case (insn_opcode)
      OpLui: begin
        // TODO: start here by implementing lui
        // logic [31:0] extended_imm;
        // extended_imm = {12'b0, insn_from_imem[31:12]};
        // extended_imm = extended_imm <<< 12;
        lui_result = imm_u_sext <<< 12;
        insn_result = lui_result;

        // set defaults
        target_branch = 32'b0;
        alt_PC = 32'b0;
        branch_ALU_input1 = 32'b0;
        branch_ALU_input2 = 32'b0;
        ALU_input1 = 0;
        ALU_input2 = 0;
      end

      OpAuipc: begin
        ALU_input1 = pc_to_imem;
        ALU_input2 = imm_u_sext <<< 12;
        insn_result = alu_result;

      end

      OpRegImm: begin

        // set defaults
        target_branch = 32'b0;
        alt_PC = 32'b0;
        branch_ALU_input1 = 32'b0;
        branch_ALU_input2 = 32'b0;
        lui_result = 0;

        case(insn_funct3)
          3'b000: begin // addi
            ALU_input1 = rs1_out; 
            // extended_rs2 = {20'b0, imm_i};
            ALU_input2 = imm_i_sext; // ALU_input2 is imm
            insn_result = alu_result;
          end
          3'b010: begin // slti
            ALU_input1 = rs1_out; 
            ALU_input2 = imm_i_sext; // ALU_input2 is imm
            insn_result = alu_result;
          end
            
          3'b011: begin // sltiu
            ALU_input1 = rs1_out; 
            ALU_input2 = $unsigned(imm_i_sext); // take unsigned version
            insn_result = alu_result;
          end

          3'b100: begin // xori
            ALU_input1 = rs1_out;
            ALU_input2 = imm_i_sext;
            insn_result = alu_result;
          end

          3'b110: begin // ori
            ALU_input1 = rs1_out;
            ALU_input2 = imm_i_sext;
            insn_result = alu_result;
          end

          3'b111: begin // andi
            ALU_input1 = rs1_out;
            ALU_input2 = imm_i_sext;
            insn_result = alu_result;
          end

          3'b001: begin // slli
            ALU_input1 = rs1_out;
            ALU_input2 = {27'b0, imm_i[4:0]};
            insn_result = alu_result;
          end

          3'b101: begin // srli and srai
            ALU_input1 = rs1_out;
            ALU_input2 = {27'b0, imm_i[4:0]};
            insn_result = alu_result;
          end

          default: begin
            ALU_input1 = 0;
            ALU_input2 = 0;
          end
        endcase
        
      end

      OpRegReg: begin // instructions involving 2 regs
        // set defaults
        target_branch = 32'b0;
        alt_PC = 32'b0;
        branch_ALU_input1 = 32'b0;
        branch_ALU_input2 = 32'b0;
        lui_result = 0;

        case (insn_funct3)
          3'b000: begin // add and sub


            case (insn_funct7)
              7'b0000000: begin // add
                ALU_input1 = rs1_out;
                ALU_input2 = rs2_out;
                insn_result = alu_result;
              end
              7'b0100000: begin // sub
                ALU_input1 = rs1_out;
                ALU_input2 = (32'b11111111111111111111111111111111 ^ rs2_out) + 1;
                insn_result = alu_result;
              end
              7'b0000001: begin // mul
                ALU_input1 = rs1_out;
                ALU_input2 = rs2_out;
                insn_result = alu_result; // gets truncated to 32 bits in alu
              end
              default: begin
                ALU_input1 = 0;
                ALU_input2 = 0;
                insn_result = 0;
              end
            endcase
          end

          3'b001: begin // sll and mulh
            case (insn_funct7)
              7'b0000000: begin // sll
                ALU_input1 = rs1_out;
                ALU_input2 = {27'b0, rs2_out[4:0]};
                insn_result = alu_result;
              end

              7'b0000001: begin // mulh
                ALU_input1 = $signed(rs1_out);
                ALU_input2 = $signed(rs2_out);
                insn_result = $signed(alu_result);
              end
              default: begin
                ALU_input1 = 0;
                ALU_input2 = 0;
                insn_result = 0;
              end
            endcase
            

          end

          3'b010: begin // slt and mulhsu
            
            case (insn_funct7)
              7'b0000000: begin // slt
                ALU_input1 = $signed(rs1_out);
                ALU_input2 = $signed(rs2_out);
                insn_result = alu_result;
              end

              7'b0000001: begin // mulhsu
                // check sign of final result
                mulhsu_sign_bit = rs1_out[31]; // since input2 is always positive

                // if rs2 is negative (31st bit is 1), then 2C it. Otherwise, keep it the same
                ALU_input1 = (rs1_out[31] == 1'b1) ? ((32'b11111111111111111111111111111111 ^ rs1_out) + 1) : $unsigned(rs1_out);
                ALU_input2 = rs2_out;
                insn_result = alu_result;

              end
              default: begin
                ALU_input1 = 0;
                ALU_input2 = 0;
                insn_result = 0;
              end
            endcase
            
          end

          3'b011: begin // sltu and mulhu

            case (insn_funct7)
              7'b0000000: begin // sltu
                ALU_input1 = rs1_out;
                ALU_input2 = $unsigned(rs2_out);
                insn_result = alu_result;
              end

              7'b0000001: begin // mulhu
                ALU_input1 = $unsigned(rs1_out);
                ALU_input2 = $unsigned(rs2_out);
                insn_result = alu_result;
              end
              default: begin
                ALU_input1 = 0;
                ALU_input2 = 0;
                insn_result = 0;
              end
            endcase
          end

          3'b100: begin // xor & div  
            case (insn_funct7)
              7'b0000000: begin // xor
                ALU_input1 = rs1_out;
                ALU_input2 = rs2_out;
                insn_result = alu_result;
              end

              7'b0000001: begin // div
                
                div_sign_bit = rs2_out == 0 ? 0 : rs1_out[31] ^ rs2_out[31]; // set 0 if div by 0
                ALU_input1 = (rs1_out[31] == 1'b1) ? ((32'b11111111111111111111111111111111 ^ rs1_out) + 1) : $unsigned(rs1_out);
                ALU_input2 = (rs2_out[31] == 1'b1) ? ((32'b11111111111111111111111111111111 ^ rs2_out) + 1) : $unsigned(rs2_out);
                insn_result = $signed(alu_result);
              end
              default: begin
                ALU_input1 = 0;
                ALU_input2 = 0;
                insn_result = 0;
              end
            endcase
          end

          3'b101: begin // srl, divu, and sra
            case (insn_funct7)
              7'b0000000: begin // srl
                ALU_input1 = rs1_out;
                ALU_input2 = {27'b0, rs2_out[4:0]};
                insn_result = alu_result;
              end

              7'b0000001: begin // divu
                ALU_input1 = rs1_out;
                ALU_input2 = rs2_out;
                insn_result = alu_result;
              end

              7'b0100000: begin // sra
                ALU_input1 = rs1_out;
                ALU_input2 = {27'b0, rs2_out[4:0]};
                insn_result = alu_result;
              end
              default: begin
                ALU_input1 = 0;
                ALU_input2 = 0;
                insn_result = 0;
              end
            endcase
          end

          3'b110: begin // or & rem
            case (insn_funct7)
              7'b0000000: begin // or
                ALU_input1 = rs1_out;
                ALU_input2 = rs2_out;
                insn_result = alu_result;
              end

              7'b0000001: begin // rem
                rem_sign_bit = rs2_out == 0 ? 0 : rs1_out[31];
                ALU_input1 = (rs1_out[31] == 1'b1) ? ((32'b11111111111111111111111111111111 ^ rs1_out) + 1) : $unsigned(rs1_out);
                ALU_input2 = (rs2_out[31] == 1'b1) ? ((32'b11111111111111111111111111111111 ^ rs2_out) + 1) : $unsigned(rs2_out);
                insn_result = $signed(alu_result);
              end
              default: begin
                ALU_input1 = 0;
                ALU_input2 = 0;
                insn_result = 0;
              end
            endcase
          end

          3'b111: begin // and & remu
            case (insn_funct7)
              7'b0000000: begin // and
                ALU_input1 = rs1_out;
                ALU_input2 = rs2_out;
                insn_result = alu_result;
              end

              7'b0000001: begin // remu
                ALU_input1 = rs1_out;
                ALU_input2 = rs2_out;
                insn_result = alu_result;
              end
              default: begin
                ALU_input1 = 0;
                ALU_input2 = 0;
                insn_result = 0;
              end
            endcase
          end

          default: begin
            ALU_input1 = 0;
            ALU_input2 = 0;
            insn_result = 0;
          end
        endcase
      end

      OpBranch: begin

        // set defaults
        ALU_input1 = 32'b0;
        ALU_input2 = 32'b0;
        lui_result = 0;
        insn_result = 0;

        target_branch = imm_b_sext;
        alt_PC = pcCurrent + target_branch;
        case (insn_funct3)

          3'b000: begin // beq
            branch_ALU_input1 = rs1_out;
            branch_ALU_input2 = rs2_out;
          end

          3'b001: begin // bne
            branch_ALU_input1 = rs1_out;
            branch_ALU_input2 = rs2_out;
          end

          3'b100: begin // blt
            branch_ALU_input1 = $signed(rs1_out);
            branch_ALU_input2 = $signed(rs2_out);
          end

          3'b101: begin // bge
            branch_ALU_input1 = $signed(rs1_out);
            branch_ALU_input2 = $signed(rs2_out);
          end

          3'b110: begin // bltu
            branch_ALU_input1 = $unsigned(rs1_out);
            branch_ALU_input2 = $unsigned(rs2_out);
          end

          3'b111: begin // bgeu
            branch_ALU_input1 = $unsigned(rs1_out);
            branch_ALU_input2 = $unsigned(rs2_out);
          end

          default: begin
              branch_ALU_input1 = 0;
              branch_ALU_input2 = 0;
          end

        endcase
      end

      OpJal: begin
        insn_result = pc_unc_inc; // rd = pc + 4 --> goes directly to rf
        ALU_input1 = pc_to_imem; // compute branch using alu since add is high num of bits
        ALU_input2 = imm_j_sext;
        alt_PC = alu_result;
      end

      OpJalr: begin
        insn_result = pc_unc_inc;
        ALU_input1 = rs1_out;
        ALU_input2 = imm_i_sext;
        alt_PC = alu_result;
      end

      OpLoad: begin
        ALU_input1 = rs1_out;
        ALU_input2 = imm_i_sext;
        addr_to_dmem = alu_result;
        store_we_to_dmem = 0; // should always be 0
        case (insn_funct3) // assign value to rd based on the load type
          3'b000: begin // lb (s-ext)
            case (offset_parity)
              2'b00: begin // 4-indexed
                insn_result = {{24{load_data_from_dmem[7]}}, load_data_from_dmem[7:0]};
              end

              2'b01: begin // 1-indexed
                insn_result = {{24{load_data_from_dmem[15]}}, load_data_from_dmem[15:8]};
              end

              2'b10: begin // 2-indexed
                insn_result = {{24{load_data_from_dmem[23]}}, load_data_from_dmem[23:16]};
              end

              2'b11: begin // 3-indexed
                insn_result = {{24{load_data_from_dmem[31]}}, load_data_from_dmem[31:24]};
              end           
            endcase         
          end

          3'b001: begin // lh (s-ext)
            // insn_result = {{16{load_data_from_dmem[15]}}, load_data_from_dmem[15:0]};
            case (offset_parity)
              2'b00: begin
                insn_result = {{16{load_data_from_dmem[15]}}, load_data_from_dmem[15:0]};
              end

              2'b10: begin
                insn_result = {{16{load_data_from_dmem[31]}}, load_data_from_dmem[31:16]};
              end

              default: begin // somehow still misaligned
                insn_result = 32'b0; 
              end
            endcase
          end

          3'b010: begin // lw
            insn_result = load_data_from_dmem;
          end

          3'b100: begin // lbu (zero-ext)
            // insn_result = {{24'b0}, load_data_from_dmem[7:0]};
            case (offset_parity)
              2'b00: begin // 4-indexed
                insn_result = {{24'b0}, load_data_from_dmem[7:0]};
              end

              2'b01: begin // 1-indexed
                insn_result = {{24'b0}, load_data_from_dmem[15:8]};
              end

              2'b10: begin // 2-indexed
                insn_result = {{24'b0}, load_data_from_dmem[23:16]};
              end

              2'b11: begin // 3-indexed
                insn_result = {{24'b0}, load_data_from_dmem[31:24]};
              end           
            endcase
          end

          3'b101: begin // lhu (zero-ext)
            // insn_result = {{16'b0}, load_data_from_dmem[15:0]};
            case (offset_parity)
              2'b00: begin
                insn_result = {{16'b0}, load_data_from_dmem[15:0]};
              end

              2'b10: begin
                insn_result = {{16'b0}, load_data_from_dmem[31:16]};
              end

              default: begin // somehow still misaligned
                insn_result = 32'b0; 
              end
            endcase
          end

          default: begin
            insn_result = 32'b0;
          end
        endcase
      end

      OpStore: begin
        ALU_input1 = rs1_out;
        ALU_input2 = imm_s_sext;
        addr_to_dmem = alu_result;
        case (insn_funct3)
          3'b000: begin // sb
            
            case (offset_parity) // apply mask mased on the offset
              2'b00: begin // 4-indexed
                // store_data_to_dmem = {{24'b0}, rs2_out[7:0]};
                store_data_to_dmem = {{24'b0}, rs2_out[7:0]};
                store_we_to_dmem = 4'b0001;
              end

              2'b01: begin // 1-indexed
                // store_data_to_dmem = {{24'b0}, rs2_out[15:8]};
                store_data_to_dmem = {{16'b0}, rs2_out[7:0], {8'b0}};
                store_we_to_dmem = 4'b0010;
              end

              2'b10: begin // 2-indexed
                // store_data_to_dmem = {{24'b0}, rs2_out[23:16]};
                store_data_to_dmem = {{8'b0}, rs2_out[7:0], {16'b0}};
                store_we_to_dmem = 4'b0100;
              end

              2'b11: begin // 3-indexed
                // store_data_to_dmem = {{24'b0}, rs2_out[31:24]};
                store_data_to_dmem = {rs2_out[7:0], {24'b0}};
                store_we_to_dmem = 4'b1000;
              end
            endcase
          end

          3'b001: begin // sh
            case (offset_parity)
              2'b00: begin
                // store_data_to_dmem = {{16'b0}, rs2_out[15:0]};
                store_data_to_dmem = {{16'b0}, rs2_out[15:0]};
                store_we_to_dmem = 4'b0011;
              end

              2'b10: begin
                // store_data_to_dmem = {{16'b0}, rs2_out[31:16]};
                store_data_to_dmem = {rs2_out[15:0], {16'b0}};
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
            store_data_to_dmem = rs2_out;
            store_we_to_dmem = 4'b1111;
          end 

          default: begin
            store_data_to_dmem = 0;
            store_we_to_dmem = 0;
          end
        endcase
      end

      OpEnviron: begin
        halt = 1;
      end

      default: begin
        illegal_insn = 1'b1;
        target_branch = 32'b0;
        alt_PC = 32'b0;
        branch_ALU_input1 = 32'b0;
        branch_ALU_input2 = 32'b0;
        ALU_input1 = 32'b0;
        ALU_input2 = 32'b0;
        lui_result = 0;
        insn_result = 0;

      end

    endcase

    

  end

  // assign insn_result based on the class of instruction
  // always_comb begin
  //   case (insn_opcode)
  //     OpLui: begin
  //       insn_result = lui_result;
  //     end

  //     OpRegImm: begin
  //       insn_result = alu_result;
  //     end

  //     default: begin
  //       illegal_insn = 1'b1;
  //     end
  //   endcase

  // end

  logic branch_decide;
  always_comb begin
    case (insn_opcode)
      OpBranch: begin
        case (insn_funct3)
          3'b000: begin // beq
            branch_decide = branch_ALU_input1 == branch_ALU_input2;
          end

          3'b001: begin // bne
            branch_decide = branch_ALU_input1 != branch_ALU_input2;
          end

          3'b100: begin // blt
            branch_decide = $signed($signed(branch_ALU_input1) < $signed(branch_ALU_input2)) ? 1 : 0;
          end

          3'b101: begin // bge
            branch_decide = $signed($signed(branch_ALU_input1) >= $signed(branch_ALU_input2)) ? 1 : 0;
          end

          3'b110: begin // bltu
            branch_decide = branch_ALU_input1 < branch_ALU_input2;
          end

          3'b111: begin // bgeu
            branch_decide = branch_ALU_input1 >= branch_ALU_input2;
          end

          default: begin
            branch_decide = 0;
          end
        endcase
      end

      OpJal: begin // always jump when Jal instruction
        branch_decide = 1;
      end

      OpJalr: begin // always jump when Jalr instruction
        branch_decide = 1;
      end

      default: begin
        branch_decide = 0; // if not a branch instruction, increment pc as normal
      end  
    endcase
  end

  wire [31:0] pc_inc;
  assign pc_inc = ((insn_div || insn_divu || insn_rem || insn_remu) && divide_state == 0) ? pcCurrent : pc_unc_inc; // only update if divide is completed

  assign pcNext = (branch_decide == 1) ? alt_PC : pc_inc; 


endmodule

module MemorySingleCycle #(
    parameter int NUM_WORDS = 512
) (
    // rst for both imem and dmem
    input wire rst,

    // clock for both imem and dmem. See RiscvProcessor for clock details.
    input wire clock_mem,

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

  always @(posedge clock_mem) begin
    if (rst) begin
    end else begin
      insn_from_imem <= mem[{pc_to_imem[AddrMsb:AddrLsb]}];
    end
  end

  always @(negedge clock_mem) begin
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

/*
This shows the relationship between clock_proc and clock_mem. The clock_mem is
phase-shifted 90° from clock_proc. You could think of one proc cycle being
broken down into 3 parts. During part 1 (which starts @posedge clock_proc)
the current PC is sent to the imem. In part 2 (starting @posedge clock_mem) we
read from imem. In part 3 (starting @negedge clock_mem) we read/write memory and
prepare register/PC updates, which occur at @posedge clock_proc.

        ____
 proc: |    |______
           ____
 mem:  ___|    |___
*/
module RiscvProcessor (
    input  wire  clock_proc,
    input  wire  clock_mem,
    input  wire  rst,
    output logic halt
);

  wire [`REG_SIZE] pc_to_imem, insn_from_imem, mem_data_addr, mem_data_loaded_value, mem_data_to_write;
  wire [3:0] mem_data_we;

  MemorySingleCycle #(
      .NUM_WORDS(8192)
  ) mem (
      .rst      (rst),
      .clock_mem (clock_mem),
      // imem is read-only
      .pc_to_imem(pc_to_imem),
      .insn_from_imem(insn_from_imem),
      // dmem is read-write
      .addr_to_dmem(mem_data_addr),
      .load_data_from_dmem(mem_data_loaded_value),
      .store_data_to_dmem (mem_data_to_write),
      .store_we_to_dmem  (mem_data_we)
  );

  DatapathMultiCycle datapath (
      .clk(clock_proc),
      .rst(rst),
      .pc_to_imem(pc_to_imem),
      .insn_from_imem(insn_from_imem),
      .addr_to_dmem(mem_data_addr),
      .store_data_to_dmem(mem_data_to_write),
      .store_we_to_dmem(mem_data_we),
      .load_data_from_dmem(mem_data_loaded_value),
      .halt(halt)
  );

endmodule
