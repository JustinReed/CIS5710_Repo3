`timescale 1ns / 1ps

/**
 * @param a first 1-bit input
 * @param b second 1-bit input
 * @param g whether a and b generate a carry
 * @param p whether a and b would propagate an incoming carry
 */
module gp1(input wire a, b,
           output wire g, p);
   assign g = a & b;
   assign p = a | b;
endmodule

/**
 * Computes aggregate generate/propagate signals over a 4-bit window.
 * @param gin incoming generate signals
 * @param pin incoming propagate signals
 * @param cin the incoming carry
 * @param gout whether these 4 bits internally would generate a carry-out (independent of cin)
 * @param pout whether these 4 bits internally would propagate an incoming carry from cin
 * @param cout the carry outs for the low-order 3 bits
 */
module gp4(input wire [3:0] gin, pin,
           input wire cin,
           output wire gout, pout,
           output wire [2:0] cout);

   // TODO: your code here
   wire p1_0; // propagate signal for bits 1 and 0
   wire g1_0; // generate signal ""
   wire p3_2; // propagate signal for bits 3 and 2
   wire g3_2; // generate signal ""

   assign p1_0 = (& pin[1:0]);
   assign g1_0 = ((gin[0] & pin[1]) | gin[1]);

   assign p3_2 = (& pin[3:2]);
   assign g3_2 = ((gin[2] & pin[3]) | gin[3]);


   // carry out signals
   wire c1;
   wire c2;
   wire c3;

   assign c1 = ((cin & pin[0]) | gin[0]);
   assign c2 = ((cin & p1_0) | g1_0);
   assign c3 = ((c2 & pin[2]) | gin[2]);
   assign cout[0] = c1;
   assign cout[1] = c2;
   assign cout[2] = c3;

   // g and p output signals
   assign pout = (p1_0 & p3_2);
   assign gout = ((p3_2 & g1_0) | g3_2);



endmodule

/** Same as gp4 but for an 8-bit window instead */
module gp8(input wire [7:0] gin, pin,
           input wire cin,
           output wire gout, pout,
           output wire [6:0] cout,
           output wire carry_last);

   // TODO: your code here
   wire p1_0; // propagate signal for bits 1 and 0
   wire g1_0; // generate signal ""
   wire p3_2; // propagate signal for bits 3 and 2
   wire g3_2; // generate signal ""
   

   assign p1_0 = (& pin[1:0]);
   assign g1_0 = ((gin[0] & pin[1]) | gin[1]);

   assign p3_2 = (& pin[3:2]);
   assign g3_2 = ((gin[2] & pin[3]) | gin[3]);


   // carry out signals
   wire c1;
   wire c2;
   wire c3;
   wire c4;

   assign c1 = ((cin & pin[0]) | gin[0]);
   assign c2 = ((cin & p1_0) | g1_0);
   assign c3 = ((c2 & pin[2]) | gin[2]);

   // g and p output signals
   wire p3_0;
   wire g3_0;
   assign p3_0 = (p1_0 & p3_2);
   assign g3_0 = ((p3_2 & g1_0) | g3_2);

   assign c4 = ((p3_0 & cin) | g3_0);

   ////////////

   wire p5_4; // propagate signal for bits 1 and 0
   wire g5_4; // generate signal ""
   wire p7_6; // propagate signal for bits 3 and 2
   wire g7_6; // generate signal ""
   

   assign p5_4 = (& pin[5:4]);
   assign g5_4 = ((gin[4] & pin[5]) | gin[5]);

   assign p7_6 = (& pin[7:6]);
   assign g7_6 = ((gin[6] & pin[7]) | gin[7]);


   // carry out signals
   wire c5;
   wire c6;
   wire c7;

   assign c5 = ((c4 & pin[4]) | gin[4]);
   assign c6 = ((c4 & p5_4) | g5_4);
   assign c7 = ((c6 & pin[6]) | gin[6]);

   // g and p output signals
   wire p7_4;
   wire g7_4;
   assign p7_4 = (p5_4 & p7_6);
   assign g7_4 = ((p7_6 & g5_4) | g7_6);

   assign cout[0] = c1;
   assign cout[1] = c2;
   assign cout[2] = c3;
   assign cout[3] = c4;
   assign cout[4] = c5;
   assign cout[5] = c6;
   assign cout[6] = c7;

   // final g and p output signals
   assign pout = (p3_0 & p7_4);
   assign gout = ((p7_4 & g3_0) | g7_4);

   assign carry_last = ((pout & cin) | gout);
   


endmodule

module cla
  (input wire [31:0]  a, b,
   input wire         cin,
   output wire [31:0] sum);


   wire [31:0] g_in_vector;
   wire [31:0] p_in_vector;


   // assign  test1234[0][4] = 1'b1;

   // instantiate all the initial p and g bit values
   genvar i; 
   genvar j;
   for (i = 0; i < 4; i = i + 1) begin: cla_circuit_part1 // for-loop: create g and p signals for gp8
      for (j = 0; j < 8; j = j + 1) begin
         gp1 curr_circuit(.a(a[8 * i + j]), .b(b[8 * i + j]), .g(g_in_vector[8 * i + j]), .p(p_in_vector[8 * i + j]));
      end
   end

   // create 4 gp8 circuits using each vector
   wire [27:0] carry_vector; // final carries, except forr intermediate carries
   // wire [4:0] carry_bridge_in; // cin, c8, c16, and c24. c32 is carry-out
   // wire [4:0] carry_bridge_out;

   wire [3:0] g_out_vector; // g7_0, g15_8, g23_16, g31_24 
   wire [3:0] p_out_vector; // p7_0, p15_8, p23_16, p31_24 
   // assign carry_bridge_in[0] = cin;
   

   // genvar k;
   // for (k = 0; k < 4; k = k + 1) begin: cla_circuit_part2
   //    gp8 curr_circuit2(.gin(g_in_vector[((k+1) * 8 - 1):(k * 8)]), .pin(p_in_vector[((k+1) * 8 - 1):(k*8)]),
   //    .cin(carry_bridge_in[k]), .gout(g_out_vector[k]), .pout(p_out_vector[k]), 
   //    .cout(carry_vector[((k+1) * 7 - 1):(k*7)]), .carry_last(carry_bridge_out[k]));
   //    assign carry_bridge_in[k+1] = carry_bridge_out[k];
      // if (k != 4 & k != -1) begin: carry_assignment
      //    // previous carry_bridge bit is the carry-in, next carry_bridge bit is assigned by the carry_out formula
         
      // end
      // previous carry_bridge bit is the carry-in, next carry_bridge bit is assigned by the carry_out formula
      

      // assign carry_bridge[k+1] = ((p_out_vector[k] & carry_bridge[k]) | g_out_vector[k]); 
      // assign carry_bridge[k+1] = ((p_out_vector[k]) | g_out_vector[k]); // uncomment to pass 5/8 tests
      // assign carry_bridge[1] = ((p_out_vector[k] & carry_bridge[0]) | g_out_vector[k]); 
   // end

   wire c8;
   gp8 gp8_1(.gin(g_in_vector[7:0]), .pin(p_in_vector[7:0]), // ls
      .cin(cin), .gout(g_out_vector[0]), .pout(p_out_vector[0]), 
      .cout(carry_vector[6:0]), .carry_last(c8));
      
   wire c16;
   gp8 gp8_2(.gin(g_in_vector[15:8]), .pin(p_in_vector[15:8]), 
      .cin(c8), .gout(g_out_vector[1]), .pout(p_out_vector[1]), 
      .cout(carry_vector[13:7]), .carry_last(c16));
   
   wire c24;
   gp8 gp8_3(.gin(g_in_vector[23:16]), .pin(p_in_vector[23:16]), 
      .cin(c16), .gout(g_out_vector[2]), .pout(p_out_vector[2]), 
      .cout(carry_vector[20:14]), .carry_last(c24));
   
   wire c32;
   gp8 gp8_4(.gin(g_in_vector[31:24]), .pin(p_in_vector[31:24]), 
      .cin(c24), .gout(g_out_vector[3]), .pout(p_out_vector[3]), 
      .cout(carry_vector[27:21]), .carry_last(c32));

   wire [31:0] final_carries ;
   // assign final_carries = {cin, carry_vector[6:0], c8, carry_vector[13:7], 
   // c16, carry_vector[20:14], c24, carry_vector[27:21]};


   assign final_carries = {carry_vector[27:21], c24, carry_vector[20:14], c16, 
   carry_vector[13:7], c8, carry_vector[6:0], cin};

   assign sum = ((a ^ b) ^ final_carries);

endmodule
