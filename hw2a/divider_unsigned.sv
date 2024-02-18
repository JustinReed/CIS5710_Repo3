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
    wire [31:0] dividend[31:0];
    assign dividend[31] = {31'b0, i_dividend[31]};

    wire [31:0] new_dividend[31:0];


    genvar i; 
    for (i = 0; i < 32; i = i + 1) begin: divider_circuit
        divu_1iter_alt curr_circuit(.curr_dividend(dividend[31 - i]), .carry_bit(i_dividend[31 - i]), 
        .total_divisor(i_divisor), .next_dividend(new_dividend[31 - i]), .quotient_bit(o_quotient[31 - i])); 
        assign dividend[30 - i] = new_dividend[31 - i];

        // assign o_quotient[i] = 1'b0;
        // assign dividend = dividend << 1;  
        // if(i = 31) begin
            
        // end
    
    end

    assign o_remainder = new_dividend[0];

endmodule

module divu_1iter_alt(
    input wire [31:0] curr_dividend, 
    input wire carry_bit, 
    input wire [31:0] total_divisor, 
    output wire [31:0] next_dividend,
    output wire quotient_bit
); 
    wire [31:0] shift_result;
    wire [31:0] dividend_compare;
    assign shift_result = {curr_dividend[30:0], carry_bit};
    assign dividend_compare = shift_result - total_divisor;

    wire is_negative;
    assign is_negative = dividend_compare[31]; // first bit of subtraction result indicates sign


    assign next_dividend = is_negative ? shift_result : dividend_compare;
    assign quotient_bit = ~ is_negative;



    



endmodule

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

    // assign o_dividend = 31'b0;    

endmodule
