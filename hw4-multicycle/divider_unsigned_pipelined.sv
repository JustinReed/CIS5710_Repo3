/* INSERT NAME AND PENNKEY HERE */

`timescale 1ns / 1ns

// quotient = dividend / divisor

typedef struct packed {
 logic [31:0] inter_dividend;
 logic [31:0] inter_new_dividend;
 logic [31:0] inter_i_divisor;
 logic [31:0] curr_quotient;
 logic [31:0] inter_i_dividend;
} inter_reg;

module divider_unsigned_pipelined (
    input wire clk, rst,
    input  wire [31:0] i_dividend,
    input  wire [31:0] i_divisor,
    output wire [31:0] o_remainder,
    output wire [31:0] o_quotient
);

    // TODO: your code here

    // wire [31:0] dividend[31:0];
    // // assign dividend[31] = {31'b0, i_dividend[31]};
    // assign dividend[31] = {i_dividend[31], 31'b0};
    
    // wire [31:0] new_dividend[31:0];
    // genvar i; 
    // for (i = 0; i < 32; i = i + 1) begin: divider_circuit
    //     divu_1iter_alt curr_circuit(.curr_dividend(dividend[31 - i]), .carry_bit(i_dividend[31 - i]), 
    //     .total_divisor(i_divisor), .next_dividend(new_dividend[31 - i]), .quotient_bit(o_quotient[31 - i])); 
    //     assign dividend[30 - i] = new_dividend[31 - i];
    // end

    // assign o_remainder = new_dividend[0];

    logic internal_PC;
    always_ff @ (posedge clk) begin
        internal_PC <= 1;
    end
    
    wire [31:0] dividend[31:0];
    assign dividend[31] = {i_dividend[31], 31'b0};
    
    wire [31:0] new_dividend[31:0];

    wire [31:0] fin_quotient;


    genvar j; 
    for (j = 0; j < 16; j = j + 1) begin: divider_circuit2
        divu_1iter_alt curr_circuit2(.curr_dividend(dividend[31 - j]), .carry_bit(i_dividend[31 - j]), 
        .total_divisor(i_divisor), .next_dividend(new_dividend[31 - j]), .quotient_bit(fin_quotient[31 - j])); 
        assign dividend[30 - j] = new_dividend[31 - j];
    end

    // the inputs used to complete the second half of the division, stored in a register
    inter_reg stage2;
    always_ff @(posedge clk) begin
        stage2.inter_dividend <= dividend[15]; 
        stage2.inter_new_dividend <= new_dividend[16];
        stage2.inter_i_divisor <= i_divisor; // divsor is unchanged
        stage2.inter_i_dividend <= i_dividend;
        stage2.curr_quotient <= fin_quotient;
    end


    wire [31:0] dividend2[15:0];
    assign dividend2[15] = stage2.inter_new_dividend;
    
    wire [31:0] new_dividend2[15:0];

    wire [15:0] fin_quotient2; 

    genvar i; 
    for (i = 0; i < 16; i = i + 1) begin: divider_circuit
        divu_1iter_alt curr_circuit(.curr_dividend(dividend2[15 - i]), .carry_bit(stage2.inter_i_dividend[15 - i]), 
        .total_divisor(stage2.inter_i_divisor), .next_dividend(new_dividend2[15 - i]), .quotient_bit(fin_quotient2[15 - i])); 
        assign dividend2[14 - i] = new_dividend2[15 - i];
    end


    
    

    assign o_quotient = {stage2.curr_quotient[31:16], fin_quotient2};
    assign o_remainder = new_dividend2[0];

endmodule


module divu_1iter_alt(
    input wire [31:0] curr_dividend, 
    input wire carry_bit, 
    input wire [31:0] total_divisor, 
    output wire [31:0] next_dividend,
    output wire quotient_bit
); 
    wire [31:0] shift_result;
    wire [32:0] dividend_compare; // need carry bit
    assign shift_result = {curr_dividend[30:0], carry_bit};

    assign dividend_compare = shift_result - total_divisor;


    wire is_negative;
    assign is_negative = dividend_compare[32]; // first bit of subtraction result indicates sign


    assign next_dividend = is_negative ? shift_result : dividend_compare[31:0];
    assign quotient_bit = ~ is_negative;

endmodule
