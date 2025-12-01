// mips_decode: a decoder for MIPS arithmetic instructions
//
// alu_op      (output) - control signal to be sent to the ALU
// writeenable (output) - should a new value be captured by the register file
// itype       (output) - should the ALU receive 1 reg. value and 1 immediate (1) or 2 reg values (0)
// except      (output) - set to 1 when we don't recognize an opdcode & funct combination
// control_type[1:0] (output) - 00 = fallthrough, 01 = branch_target, 10 = jump_target, 11 = jump_register 
// mem_read    (output) - the register value written is coming from the memory
// word_we     (output) - we're writing a word's worth of data
// byte_we     (output) - we're only writing a byte's worth of data
// byte_load   (output) - we're doing a byte load
// lui         (output) - the instruction is a lui
// slt         (output) - the instruction is an slt
// opcode       (input) - the opcode field from the instruction
// funct        (input) - the function field from the instruction
// zero         (input) - from the ALU
//

module mips_decode(alu_op, writeenable, itype, except, control_type,
		   mem_read, word_we, byte_we, byte_load, lui, slt, 
		   opcode, funct, zero);
   output reg [2:0] alu_op; // not a register actually, I just want to use case
   output reg except; // same thing here
   output 	writeenable, itype;
   output reg [1:0] control_type;
   output 	mem_read, word_we, byte_we, byte_load, lui, slt;
   input  [5:0] opcode, funct;
   input 	zero;
   
   // set alu_op, except, control_type
    always @ (*) begin
        except = 0;
        alu_op = `ALU_ADD; // default value
        control_type = 2'b00;
        if (opcode == 0) begin
            case (funct)
                `OP0_ADD, `OP0_ADDU: alu_op = `ALU_ADD;
                `OP0_SUB, `OP0_SUBU, `OP0_SLT, `OP0_SLTU: alu_op = `ALU_SUB;
                `OP0_AND: alu_op = `ALU_AND;
                `OP0_OR:  alu_op = `ALU_OR;
                `OP0_NOR: alu_op = `ALU_NOR;
                `OP0_XOR: alu_op = `ALU_XOR;
                `OP0_JR: begin
                    control_type = 2'd3;
                end
                default: except = 1;
            endcase
        end else begin
            case (opcode)
                `OP_LW, `OP_SW, `OP_ADDI, `OP_ADDIU, `OP_LB, `OP_LBU, `OP_SB: alu_op = `ALU_ADD;
                `OP_BEQ, `OP_BNE: begin
                    alu_op = `ALU_SUB;
                    control_type = 2'd1;
                end
                `OP_ANDI: alu_op = `ALU_AND;
                `OP_ORI:  alu_op = `ALU_OR;
                `OP_XORI: alu_op = `ALU_XOR;
                // `OP_NORI: alu_op = `ALU_NOR; // I guess this doesnt exist

                `OP_J, `OP_JAL: begin
                    control_type = 2'd2;
                end
                `OP_LUI: alu_op = `ALU_AND; // don't care but not default
                default: except = 1;
            endcase
        end
    
    end
    
    wire r_type_write;
    assign r_type_write = (opcode == `OP_OTHER0) && (
       (funct == `OP0_SLL) || (funct == `OP0_SRL) || (funct == `OP0_SRA)
       || (funct == `OP0_SLLV) || (funct == `OP0_SRLV) || (funct == `OP0_SRAV)
       || (funct == `OP0_MFHI) || (funct == `OP0_MFLO)
       || (funct == `OP0_ADD) || (funct  == `OP0_ADDU) || (funct == `OP0_SUB) || (funct == `OP0_SUBU)
       || (funct == `OP0_AND) || (funct == `OP0_OR) || (funct == `OP0_XOR) || (funct == `OP0_NOR)
       || (funct == `OP0_SLT) || (funct == `OP0_SLTU)
       || (funct == `OP0_JALR)
       );
    wire alu_write;
    assign alu_write = (opcode == `OP_ADDI) || (opcode == `OP_ADDIU) || (opcode == `OP_ANDI)
       || (opcode == `OP_ORI) || (opcode == `OP_XORI) || (opcode == `OP_SLTI)
       || (opcode == `OP_SLTIU) || (opcode == `OP_LUI);

    wire loads;
    assign loads = (opcode == `OP_LW) || (opcode == `OP_LB) || (opcode == `OP_LBU)
       || (opcode == `OP_LH) || (opcode == `OP_LHU) || (opcode == `OP_LWL) || (opcode == `OP_LWR);
    
    assign writeenable = r_type_write || alu_write || loads || (opcode == `OP_JAL);
    
    // set itype. I believe this works. Might be a few exceptions, we can find them later.
    assign itype = ( opcode >= 4 );


    assign mem_read = loads;
    assign word_we = (opcode == `OP_SW);
    assign byte_we = (opcode == `OP_SB);
    assign byte_load = (opcode == `OP_LB) || (opcode == `OP_LBU);
    assign lui = (opcode == `OP_LUI);
    assign slt = ((opcode == `OP_OTHER0) && (funct == `OP0_SLT || funct == `OP0_SLTU)) || (opcode == `OP_SLTI) || (opcode == `OP_SLTIU);
 

endmodule // mips_decode

module sign_extender_16to32 (in, out);
    input [15:0] in;
    output [31:0] out;

    assign out = { {16{in[15]}} , in[15:0] };
endmodule // sign_extender

module left_shifter_two (in, out);
    input [29:0] in;
    output [31:0] out;
    assign out = {in, 2'b00};
endmodule // left_shifter

module adder_ALU (A, B, out);
    output [31:0] out;
    input [31:0] A;
    input [31:0] B;

    assign out = A + B;
endmodule // adder_ALU


// full_machine: execute a series of MIPS instructions from an instruction cache
//
// except (output) - set to 1 when an unrecognized instruction is to be executed.
// clk     (input) - the clock signal
// reset   (input) - set to 1 to set all registers to zero, set to 0 for normal execution.

module full_machine(except, clk, reset);
    output 	except;
    input   clk, reset;

   // NOTE: The #(32) is setting the width for the modules. See parameter in module
   // definitions


// BEGIN Declaring Wires (sorry its a mess)

    wire [31:0]	inst;  
    wire [31:0]	PC, nextPC;
    wire [4:0]  r_dest;
    wire [31:0] rsData, rtData, rdData;
    wire        zero, negative, overflow; // flags output from main ALU, zero goes to the decoder
    wire [31:0] alu_writeback_word; // ALU output after the slt mux
    wire [31:0] mem_writeback_word; // memory output after the byte_load mux
    wire [31:0] writeback_word; // writeback value either from ALU or memory
    wire [31:0] branch_offset;
    wire [31:0] data_out; // output from main data memory
    wire [7:0]  data_out_byte; // 1 byte output from main data memory
    wire [31:0] adder1_out, adder2_out;

    // decoder signals
    wire [2:0]  alu_op;
    wire        wr_enable, itype, except, mem_read, word_we,
                byte_we, byte_load, lui, slt;

    wire [1:0]  control_type;
    wire [31:0] ALU_inB, sign_ext_out, out; // out is ALU out.

// END declaring wires


// BEGIN PC register, control type, and instruction memory

    register #(32) PC_reg(PC, nextPC, clk, 1'b1, reset); 

    adder_ALU adder1 (PC, 32'd4, adder1_out);
    adder_ALU adder2 (adder1_out, branch_offset, adder2_out);

    mux4v #(32) control_type_mux (nextPC, adder1_out, adder2_out, 
               {PC[31:28], inst[25:0], 2'b00}, rsData, control_type);

    instruction_memory inst_mem (PC[31:2], inst);

// END PC register, control type, and instruction memory
  

// BEGIN register file and ALU zone

    regfile rf (inst[25:21], inst[20:16], r_dest, rsData, rtData, rdData, wr_enable,
               clk, reset);

    // this is the mux between instruction and regfile
    mux2v #(5) rd_mux (r_dest, inst[15:11], inst[20:16], itype);
    // this is the mux between regfile and ALU
    mux2v #(32) ALU_inB_mux (ALU_inB, rtData, sign_ext_out, itype);

    alu32 mainALU (out, overflow, zero, negative, rsData, ALU_inB, alu_op[2:0]);

    // mux setting the ALU output or the slt value to the writeback rdData path
    mux2v #(32) slt_mux (alu_writeback_word, out, {31'b0, negative}, slt);

// END register file and ALU zone


// BEGIN Data Memory to rdData

    data_mem data_memory (data_out, out, rtData, word_we, byte_we, clk, reset);

    mux4v #(8) data_out_byte_mux (data_out_byte, data_out[7:0], data_out[15:8], 
               data_out[23:16], data_out[31:24], out[1:0]);
    mux2v #(32) byteload_mux (mem_writeback_word, data_out, {24'b0, data_out_byte}, byte_load);
    
    mux2v #(32) mem_read_mux (writeback_word, alu_writeback_word, mem_writeback_word, mem_read);
    mux2v #(32) lui_mux (rdData, writeback_word, {inst[15:0], 16'b0}, lui );

// END Data Memory to rdData


// BEGIN Decoder, sign extender, and shifter

    mips_decode decoder (alu_op, wr_enable, itype, except, control_type,
		   mem_read, word_we, byte_we, byte_load, lui, slt, 
		   inst[31:26], inst[5:0], zero);

    sign_extender_16to32 signext (inst[15:0], sign_ext_out);

    left_shifter_two shifter (sign_ext_out[29:0], branch_offset);

// END Decoder, sign extender, and shifter


endmodule // full_machine
