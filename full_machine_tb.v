`include "mips_defines.v"
`include "rf.v"
`include "alu32.v"
`include "rom.v"
`include "mux_lib.v"
`include "full_machine.v"

module test;
   /* Make a regular pulsing clock. */
   reg       clk = 0;
   always #5 clk = !clk;
   integer     i;

   reg 		reset = 1, done = 0;
   wire         except;

   full_machine fm(except, clk, reset);
   
   initial begin
      $dumpfile("fm.vcd");
      $dumpvars(0, test);
      # 3 reset = 0;
      # 300 done = 1;
   end
   
  initial
     $monitor("At time %t, reset = %d pc = %h, inst = %h, except = %h",
              $time, reset, fm.PC, fm.inst, except);

   // periodically check for the end of simulation.  When it happens
   // dump the register file contents.
   always @(negedge clk)
     begin
	#0;
	if ((done === 1'b1) | (except === 1'b1))
	begin
           $display ( "Dumping register state: " );
	   $display ( "  Register :  hex-value (  dec-value )" );
           for (i = 0 ; i < 32 ; i = i + 1)
 	     $display ( "%d: 0x%x ( %d )", i, fm.rf.r[i], fm.rf.r[i]);
           $display ( "Done.  Simulation ending." );
	   $finish;
	end
     end

   
endmodule // test
