/* INSERT NAME AND PENNKEY HERE */

`timescale 1ns / 1ns

// quotient = dividend / divisor

module divider_unsigned (
    input  wire [31:0] i_dividend,
    input  wire [31:0] i_divisor,
    output wire [31:0] o_remainder,
    output wire [31:0] o_quotient
);

    // TODO: your code here
// begin
//     logic temp_select = 1'b0;
//     logic test_output;
//     mux1s32b (.select(temp_select), .opt1(i_dividend), .opt2(i_divisor), .result(test_output));
    
// end    

endmodule

// module mux1s32b (select, opt1, opt2, result);
// begin
//     input select;
//     input [31:0] opt1, opt2;
//     output [31:0] result;
//     assign result = ~select & opt1 | select & opt2;
// end 
// endmodule

module divu_1iter (
    input  wire [31:0] i_dividend,
    input  wire [31:0] i_divisor,
    input  wire [31:0] i_remainder,
    input  wire [31:0] i_quotient,
    output wire [31:0] o_dividend,
    output wire [31:0] o_remainder,
    output wire [31:0] o_quotient
);
  /*
    for (int i = 0; i < 32; i++) {
        remainder = (remainder << 1) | ((dividend >> 31) & 0x1);
        if (remainder < divisor) {
            quotient = (quotient << 1);
        } else {
            quotient = (quotient << 1) | 0x1;
            remainder = remainder - divisor;
        }
        dividend = dividend << 1;
    }
    */

    // TODO: your code here

endmodule
