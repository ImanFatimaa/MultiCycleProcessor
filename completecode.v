
module MultiCycleCPU(clk, reset);

  input clk, reset;

  wire PCWrite, PCWriteCond, IRWrite, DMEMWrite, RegWrite, ALUSrcA, RegReadSel;
  wire [1:0] MemtoReg, ALUSrcB, PCSource;
  wire [3:0] ALUSel;
  wire [5:0] opcode;

  datapath	cpu_datapath(clk, reset, PCWrite, PCWriteCond, IRWrite, DMEMWrite,
                         RegWrite, ALUSrcA, RegReadSel, MemtoReg, ALUSrcB,
                         PCSource, ALUSel, opcode);

  controller	cpu_controller(opcode, clk, reset, PCWrite, PCWriteCond,
                             DMEMWrite, IRWrite, MemtoReg, PCSource, ALUSel,
                             ALUSrcA, ALUSrcB, RegWrite, RegReadSel);
endmodule

module DMem(WriteData,   // Input data into the memory
            MemData,     // Output data from the memory
            Address,     // Address of data to be read/written
            MemWrite,    // When high, causes write to take place on posedge
            Clk);        // Clock

  parameter ADDRESS_WIDTH = 9;
  parameter DATA_WIDTH = 32;

  input Clk;
  input [DATA_WIDTH-1:0]    WriteData;
  input [ADDRESS_WIDTH-1:0] Address;
  input MemWrite;
  output [DATA_WIDTH-1:0] MemData;
  
  reg [DATA_WIDTH-1:0] mem_contents [ADDRESS_WIDTH-1:0];
  integer i;

  assign MemData= mem_contents[Address];

  always @(posedge Clk)
  begin
    if(MemWrite)
    begin
      mem_contents[Address] <= #5 WriteData;
    end
  end
endmodule

module IMem(PC,Instruction);
  
  input [31:0] PC;
  output [31:0] Instruction;
  reg [31:0] Instruction;

  always @(PC)
  begin
    case(PC)
      // ADD  $R3, $R0, $R2
      0: Instruction=  32'b010010_00011_00000_00010_00000000000;

       // SUB  $R6, $R2, $R0: ALUOutput = 1 - (-2) = 3
      1: Instruction=  32'b010011_00110_00010_00000_00000000000;
      // OR   $R7, $R1, $R0: ALUOutput = (0x00010001 | 0xFFFFFFFE) = 0xFFFFFFFF
      2: Instruction= 32'b010100_00111_00001_00000_00000000000;
      // AND  $R8, $R1, $R0: ALUOutput = (0x00010001 & 0xFFFFFFFE) = 0x00010000
      3: Instruction= 32'b010101_01000_00001_00000_00000000000;
      // SLT  $R31, $R0, $R1
      4: Instruction= 32'b010111_11111_00000_00001_00000000000;

       // LW  $R19, $R0[0x0001]
      5: Instruction= 32'b111101_10011_00000_0000000000000001;
      // SW  $R0, $R0[0x1]
      6: Instruction=  32'b111110_00000_00000_0000000000000001;
      
      // BEQ
      7: Instruction= 32'b100000_00010_00001_1111111111111101; //``````````````

      // Jump 21	/ should skip the two addi 5 and go to addi 7
      8: Instruction= 32'b000001_00000_00000_0000000000000010;
      
      default: Instruction= 0; //NOOP
    endcase
  end
endmodule
module controller(opcode, clk, reset, PCWrite, PCWriteCond, DMEMWrite, IRWrite,
                   MemtoReg, PCSource, ALUSel, ALUSrcA, ALUSrcB, RegWrite,
                   RegReadSel);

  // opcode, clock, and reset inputs
  input [5:0] opcode;	// from instruction register
  input	clk, reset;

  // control signal outputs
  output reg PCWrite, PCWriteCond, DMEMWrite, IRWrite, ALUSrcA, RegWrite, RegReadSel;
  output reg [1:0] MemtoReg, PCSource, ALUSrcB;
  output reg [3:0] ALUSel;

  // 4-bit state register
  reg [3:0]	state;

  // state parameters
  parameter s0  = 4'd0;
  parameter s1  = 4'd1;
  parameter s2  = 4'd2;
  parameter s3  = 4'd3;
  parameter s4  = 4'd4;
  parameter s5  = 4'd5;
  parameter s6  = 4'd6;
  parameter s7  = 4'd7;
  parameter s8  = 4'd8;
  parameter s9  = 4'd9;
  parameter s10 = 4'd10;
  parameter s11 = 4'd11;
  parameter s12 = 4'd12;
  parameter sR  = 4'd13;	// reset
  parameter s14 = 4'd14;

  // opcode[5:4] parameters
  parameter J  = 2'b00;	// Jump or NOP
  parameter R  = 2'b01;	// R-type
  parameter BR = 2'b10;	// Branch
  parameter I  = 2'b11;	// I-type

  // I-type opcode[3:0] variations
  parameter ADDI = 4'b0010, SUBI = 4'b0011, ORI	 = 4'b0100,ANDI = 4'b0101,XORI = 4'b0110;
  parameter SLTI = 4'b0111, LI = 4'b1001, LUI = 4'b1010, LWI = 4'b1011,SWI= 4'b1100;

  // control state register
  always @(posedge clk) begin

    // check for reset signal. If set, write zero to PC and switch to Reset State on next CC.
    if (reset) begin
      PCWrite 		<= 1;
      PCWriteCond <= 0;
      DMEMWrite 	<= 0;
      IRWrite 		<= 0;
      MemtoReg 		<= 0;
      PCSource 		<= 2'b11; // reset
      ALUSel 			<= 0;
      ALUSrcA 		<= 0;
      ALUSrcB 		<= 0;
      RegWrite 		<= 0;

      state <= sR;
    end
    else begin	// if reset signal is not set, check state at pos edge
      case (state)

        // if in reset state (and reset signal not set), go to s0 (IF)
        sR: begin
          PCWrite 		<= 1;
          DMEMWrite 	<= 0;
          IRWrite 		<= 1;
          PCSource 		<= 2'b00;
          ALUSel 			<= 4'b0010;
          ALUSrcA 		<= 0;
          ALUSrcB 		<= 2'b01;
          RegWrite 		<= 0;
          PCWriteCond <= 0;

          state <= s0;
        end

        // if in s0, go to s1 (ID)
        s0: begin
          PCWrite 		<= 0;
          DMEMWrite 	<= 0;
          IRWrite 		<= 0;
          ALUSel 			<= 4'b0010;
          ALUSrcA 		<= 0;
          ALUSrcB 		<= 2'b10;
          RegWrite 		<= 0;
          RegReadSel	<= 0;

          state <= s1;
        end

        // if in s1 (ID) check opcode from instruction register to determine new state
        s1: begin
          case (opcode[5:4])
            // R-type opcode: go to s2 (R-type EX)
            R: begin
              PCWrite 		<= 0;
              DMEMWrite 	<= 0;
              IRWrite 		<= 0;
              ALUSel 			<= opcode[3:0];
              ALUSrcA 		<= 1;
              ALUSrcB 		<= 2'b00;
              RegWrite 		<= 0;

              state <= s2;
            end

            // J-type or NOP
            J: begin
              // NOP: do nothing and go back to s0 (IF) for next instruction
              if (opcode[3:0] == 4'b0000) begin
                PCWrite 		<= 1;
                DMEMWrite 	<= 0;
                IRWrite 		<= 1;
                PCSource 		<= 2'b00;
                ALUSel 			<= 4'b0010;
                ALUSrcA 		<= 0;
                ALUSrcB 		<= 2'b01;
                RegWrite 		<= 0;
                PCWriteCond <= 0;

                state	<= 0;
              end
              // Jump: go to s12 (jump completion)
              else begin
                PCWrite 		<= 1;
                DMEMWrite 	<= 0;
                IRWrite 		<= 0;
                PCSource 		<= 2'b10;
                RegWrite 		<= 0;

                state <= s12;
              end
            end

            // Branch: go to s14 ($R1 read)
            BR: begin
              PCWrite 		<= 0;
              DMEMWrite 	<= 0;
              IRWrite 		<= 0;
              ALUSel 			<= 4'b0010;
              ALUSrcA 		<= 0;
              ALUSrcB 		<= 2'b10;
              RegWrite 		<= 0;
              RegReadSel	<= 1; // for R1

              state <= s14;
            end

            // I-type
            I: begin
            // go to s3 (EX for ALU I-type with sign extended immediate)
              if ((opcode[3:0] == ADDI) || (opcode[3:0] == SUBI) || (opcode[3:0] == SLTI)) begin
                PCWrite 		<= 0;
                DMEMWrite 	<= 0;
                IRWrite 		<= 0;
                ALUSel 			<= opcode[3:0];
                ALUSrcA 		<= 1;
                ALUSrcB 		<= 2'b10;
                RegWrite 		<= 0;

                state <= s3;
              end

              // go to s4 (EX for ALU I-type with zero extended immediate)
              else if ((opcode[3:0] == ORI) || (opcode[3:0] == ANDI) || (opcode[3:0] == XORI)) begin
                PCWrite 		<= 0;
                DMEMWrite 	<= 0;
                IRWrite 		<= 0;
                ALUSel 			<= opcode[3:0];
                ALUSrcA 		<= 1;
                ALUSrcB 		<= 2'b11;
                RegWrite 		<= 0;

                state <= s4;
              end

                // go to s5 (MEM access for LWI)
              else if (opcode[3:0] == LWI) begin
                PCWrite 		<= 0;
                DMEMWrite 	<= 0;
                IRWrite 		<= 0;
                RegWrite 		<= 0;

                state <= s5;
              end
              // go to s14 for R1 read
              else if ((opcode[3:0] == LI) || (opcode[3:0] == LUI) || (opcode[3:0] == SWI))begin
                PCWrite 		<= 0;
                DMEMWrite 	<= 0;
                IRWrite 		<= 0;
                ALUSel 			<= 4'b0010;
                ALUSrcA 		<= 0;
                ALUSrcB 		<= 2'b10;
                RegWrite 		<= 0;
                RegReadSel	<= 1; // for R1

                state <= s14;
              end
            end
          endcase
        end

        // if in s2 (R-type EX) go to s6 (ALUOp write backs)
        s2: begin
          PCWrite 		<= 0;
          DMEMWrite 	<= 0;
          IRWrite 		<= 0;
          MemtoReg 		<= 2'b00;
          RegWrite 		<= 1;

          state <= s6;
        end

        // if in s3 (EX for Arithmetic I-type with sign extended Imm) go to s6 (ALUOp WB)
        s3: begin
          PCWrite 		<= 0;
          DMEMWrite 	<= 0;
          IRWrite 		<= 0;
          MemtoReg 		<= 2'b00;
          RegWrite 		<= 1;

          state <= s6;
        end

        // if in s4 (EX for Arithmetic I-type with zero extended Imm) go to s6 (ALUOp WB)
        s4: begin
          PCWrite 		<= 0;
          DMEMWrite 	<= 0;
          IRWrite 		<= 0;
          MemtoReg 		<= 2'b00;
          RegWrite 		<= 1;

          state <= s6;
        end

        // if in s5 (LWI MEM access) go to s7 (Reg File WB for LWI)
        s5: begin
          PCWrite 		<= 0;
          DMEMWrite 	<= 0;
          IRWrite 		<= 0;
          MemtoReg 		<= 2'b01;
          RegWrite 		<= 1;

          state <= s7;
        end

        // if in s6 (ALUOut WB) go back to s0 (IF)
        s6: begin
          PCWrite 		<= 1;
          DMEMWrite 	<= 0;
          IRWrite 		<= 1;
          PCSource 		<= 2'b00;
          ALUSel 			<= 4'b0010;
          ALUSrcA 		<= 0;
          ALUSrcB 		<= 2'b01;
          RegWrite 		<= 0;
          PCWriteCond <= 0;

          state <= s0;
        end

        // if in s7 (Reg Gile WB for LWI) go to s0 (IF)
        s7: begin
          PCWrite 		<= 1;
          DMEMWrite 	<= 0;
          IRWrite 		<= 1;
          PCSource 		<= 2'b00;
          ALUSel 			<= 4'b0010;
          ALUSrcA 		<= 0;
          ALUSrcB 		<= 2'b01;
          RegWrite 		<= 0;
          PCWriteCond <= 0;

          state <= s0;
        end

        // if in s8 (MEM write for SWI) go to s0 (IF)
        s8: begin
          PCWrite 		<= 1;
          DMEMWrite 	<= 0;
          IRWrite 		<= 1;
          PCSource 		<= 2'b00;
          ALUSel 			<= 4'b0010;
          ALUSrcA 		<= 0;
          ALUSrcB 		<= 2'b01;
          RegWrite 		<= 0;
          PCWriteCond <= 0;

          state <= s0;
        end

        // if in s9 (Reg WB for LI) go to s0 (IF)
        s9: begin
          PCWrite 		<= 1;
          DMEMWrite 	<= 0;
          IRWrite 		<= 1;
          PCSource 		<= 2'b00;
          ALUSel 			<= 4'b0010;
          ALUSrcA 		<= 0;
          ALUSrcB 		<= 2'b01;
          RegWrite 		<= 0;
          PCWriteCond <= 0;

          state <= s0;
        end

        // if in s10 (Reg WB for LUI) go to s0 (IF)
        s10: begin
          PCWrite 		<= 1;
          DMEMWrite 	<= 0;
          IRWrite 		<= 1;
          PCSource 		<= 2'b00;
          ALUSel 			<= 4'b0010;
          ALUSrcA 		<= 0;
          ALUSrcB 		<= 2'b01;
          RegWrite 		<= 0;
          PCWriteCond <= 0;

          state <= s0;
        end

        // if in s11 (Branch completion) go to s0 (IF)
        s11: begin
          PCWrite 		<= 1;
          DMEMWrite 	<= 0;
          IRWrite 		<= 1;
          PCSource 		<= 2'b00;
          ALUSel 			<= 4'b0010;
          ALUSrcA 		<= 0;
          ALUSrcB 		<= 2'b01;
          RegWrite 		<= 0;
          PCWriteCond <= 0;

          state <= s0;
        end

        // if in s12 (Jump completion) go to s0 (IF)
        s12: begin
          PCWrite 		<= 1;
          DMEMWrite 	<= 0;
          IRWrite 		<= 1;
          PCSource 		<= 2'b00;
          ALUSel 			<= 4'b0010;
          ALUSrcA 		<= 0;
          ALUSrcB 		<= 2'b01;
          RegWrite 		<= 0;
          PCWriteCond <= 0;

          state <= s0;
        end

        // if in R1 read
        s14: begin
          // if Branch, go to s11, branch completion
          if (opcode[5:4] == BR) begin
            PCWrite 		<= 0;
            PCWriteCond <= 1;
            DMEMWrite 	<= 0;
            IRWrite 		<= 0;
            PCSource 		<= 2'b01;
            ALUSel 			<= 4'b0011;
            ALUSrcA 		<= 1;
            ALUSrcB 		<= 2'b00;
            RegWrite 		<= 0;
            RegReadSel	<= 1;

            state <= s11;
          end
          // if LI, go to s9 LI WB
          if (opcode[3:0] == LI) begin
            PCWrite 		<= 0;
            DMEMWrite 	<= 0;
            IRWrite 		<= 0;
            MemtoReg 		<= 2'b10;
            RegWrite 		<= 1;

            state <= s9;
          end
          // if LUI, go to s10 LUI WB
          else if (opcode[3:0] == LUI) begin
            PCWrite 		<= 0;
            DMEMWrite 	<= 0;
            IRWrite 		<= 0;
            MemtoReg 		<= 2'b11;
            RegWrite 		<= 1;

            state <= s10;
          end
          // if SWI, go to s8, Mem Access
          else if (opcode[3:0] == SWI) begin
            PCWrite 		<= 0;
            DMEMWrite 	<= 1;
            IRWrite 		<= 0;
            RegWrite 		<= 0;

            state <= s8;
          end
        end
        // go to s0
        default: begin
          PCWrite 		<= 1;
          DMEMWrite 	<= 0;
          IRWrite 		<= 1;
          PCSource 		<= 2'b00;
          ALUSel 			<= 4'b0010;
          ALUSrcA 		<= 0;
          ALUSrcB 		<= 2'b01;
          RegWrite 		<= 0;
          PCWriteCond <= 0;

          state <= s0;
        end
      endcase
    end
  end
endmodule

module datapath(clk, reset, PCWrite, PCWriteCond, IRWrite, DMEMWrite, RegWrite,
                 ALUSrcA, RegReadSel, MemtoReg, ALUSrcB, PCSource, ALUSel,
                 opcode);

  input PCWrite, PCWriteCond, IRWrite, DMEMWrite, RegWrite, ALUSrcA, RegReadSel /* 0 for R3, 1 for R1*/;
  input [1:0] MemtoReg, ALUSrcB, PCSource;
  input [3:0] ALUSel;
  input clk, reset;
  output [5:0] opcode;

  parameter word_size = 32;

  // PC
  wire [word_size-1:0] PCin;
  wire [word_size-1:0] PCout;

  // Instruction Memory
  wire [word_size-1:0] IMout;

  // Instruction Register
  wire [word_size-1:0] IRout;
  wire [15:0] immediate;

  // Data Memory
  wire [word_size-1:0] DMout;

  // Memory Data Register
  wire [word_size-1:0] MDRout;

  // Sign/Zero Extension
  wire [word_size-1:0] immZE, immSE;

  // Reg File
  wire [4:0] read_sel_1, read_sel_2, write_address;
  wire [word_size-1:0] write_data;
  wire [word_size-1:0] read_data_1, read_data_2;

  // A and B outputs
  wire [word_size-1:0] Aout, Bout;

  // Jump ALU
  wire [word_size-1:0] jump_target;

  // ALU
  wire [word_size-1:0] sourceA, sourceB;
  wire [word_size-1:0] ALU_wire;
  wire zero;

  // ALUOut
  wire [word_size-1:0] ALUOut_wire;

  wire	w1;
  and	and1(w1, PCWriteCond, zero);
  or or1(PCWrite_datapath, w1, PCWrite);

  assign opcode = IRout[31:26];
  assign immediate = IRout[15:0];
  assign write_address = IRout[25:21]; // R1
  assign read_sel_1 = IRout[20:16]; // R2

  // INSTRUCTION MEM
  IMem IM(PCout, IMout);

  // DATA MEM
  DMem DM(Bout, DMout, immediate, DMEMWrite, clk);

  // MEM DATA REGISTER
  holding_reg MDR(MDRout, DMout, 1'b1, clk, reset);

  // Reg File
  nbit_register_file RF(write_data, read_data_1, read_data_2, read_sel_1, read_sel_2, write_address, RegWrite, clk);

  // PC
  holding_reg	PC(PCout, PCin, PCWrite_datapath, clk, reset);

  // INSTRUCTION REGISTER
  holding_reg IR(IRout, IMout, IRWrite, clk, reset);

  // A and B
  holding_reg	A(Aout, read_data_1, 1'b1, clk, reset);
  holding_reg B(Bout, read_data_2, 1'b1, clk, reset);

  // ALUOut Register
  holding_reg	ALUOut(ALUOut_wire, ALU_wire, 1'b1, clk, reset);

  // ZE(imm) and SE(imm)
  zero_extend	ZE(immediate, immZE);
  sign_extend SE(immediate, immSE);

  // Reg File inputs
  read_mux	read_sel_mux(read_sel_2, IRout[15:11], IRout[25:21], RegReadSel); //B is R3 or R1
  mux_2bit write_data_mux(write_data, ALUOut_wire, MDRout, {read_data_2[31:16],immediate}, {immediate,read_data_2[15:0]}, MemtoReg);

  // ALU inputs
  mux_1bit ALUSrcA_mux(sourceA, PCout, Aout, ALUSrcA); // alusrca = 0 -> sourceA = pc
  mux_2bit ALUSrcB_mux(sourceB, Bout, 32'd1, immSE, immZE, ALUSrcB);

  //PC source mux
  mux_2bit	PC_mux(PCin, ALU_wire, ALUOut_wire, jump_target, 32'h00000000, PCSource);

  //jump_target, inputPC, offset
  jumpALU	jALU(jump_target, PCout, immSE);

  // ALU
  myALU	mainALU(ALU_wire, zero, sourceA, sourceB, ALUSel);
endmodule

// Registers for PC, IR, A, B, ALUOut
module holding_reg(output_data, input_data, write, clk, reset);
  // data size
  parameter word_size = 32;

  input [word_size-1:0] input_data;
  input	write, clk, reset;
  output [word_size-1:0] output_data;

  // Register content and output assignment
  reg [word_size-1:0] content;
  assign output_data = content;

  // update regisiter contents
  always @(posedge clk) begin
    if (reset) begin
      content <= 0;
    end
    else if (write) begin
      content <= input_data;
    end
  end
endmodule

// ALU for jump target calculations
module jumpALU(jump_target, inputPC, offset);
  parameter word_size = 32;

  input [word_size-1:0] inputPC, offset;
  output [word_size-1:0] jump_target;

  assign jump_target = inputPC + offset;
endmodule

// Mulitiplexer for selecting from two 32-bit inputs
module mux_1bit(output_data, input_data0, input_data1, select);
  parameter word_size = 32;

  input select;
  input [word_size-1:0] input_data0, input_data1;

  output reg [word_size-1:0] output_data;

  // select the input
  always @(select or input_data0 or input_data1) begin
    case (select)
      0: output_data <= input_data0;
      1: output_data <= input_data1;
      default: output_data <= 0;
    endcase
  end
endmodule

// Multiplexer for choosing between four 32-bit inputs
module mux_2bit(output_data, input_data0, input_data1, input_data2, input_data3, select);
  parameter word_size = 32;

  input [1:0] select;
  input [word_size-1:0] input_data0, input_data1, input_data2, input_data3;

  output reg [word_size-1:0] output_data;

  // select the input
  always @(input_data0 or input_data1 or input_data2 or input_data3 or select) begin
    case (select)
      0: output_data <= input_data0;
      1: output_data <= input_data1;
      2: output_data <= input_data2;
      3: output_data <= input_data3;
      default: output_data <= 0;
    endcase
  end
endmodule

// Main ALU
module myALU(output_data, zero, sourceA, sourceB, ALUSel);
  parameter word_size = 32;

  input [word_size-1:0] sourceA, sourceB;
  input [3:0] ALUSel;

  output reg [word_size-1:0] output_data;
  output reg zero;

  // if any input changes, update output
  always @(sourceA, sourceB, ALUSel) begin
    // operation depends on ALUSel input
    case (ALUSel)
      4'h0: output_data = sourceA;
      4'h1: output_data = ~sourceA;
      4'h2: output_data = sourceA + sourceB;
      4'h3: begin
        output_data = sourceA - sourceB;
        if ((sourceA - sourceB) == 0) begin
          zero = 1;
        end
        else begin
          zero = 0;
        end
      end
      4'h4: output_data = sourceA | sourceB;
      4'h5: output_data = sourceA & sourceB;
      4'h6: output_data = sourceA ^ sourceB;
      4'h7: output_data = ($signed(sourceA) < $signed(sourceB))? 1 : 0;
      default: output_data = 0;
    endcase
  end
endmodule

module nbit_register_file(
  write_data,
  read_data_1, read_data_2,
  read_sel_1, read_sel_2,
  write_address, RegWrite, clk);

    parameter data_width = 32;
    parameter select_width = 5;

    input                                       clk, RegWrite;
    input           [data_width-1:0]            write_data;
    input           [4:0]                       read_sel_1, read_sel_2, write_address;
    output		     [data_width-1:0]            read_data_1, read_data_2;

    reg             [data_width-1:0]            register_file [0:data_width-1];

    integer i;
    initial begin
        for (i = 0; i < 32; i = i + 1) begin
            register_file[i] = 32'd0;
        end
    end

   assign		read_data_1 = register_file[read_sel_1];
   assign		read_data_2 = register_file[read_sel_2];

    always @ (posedge clk) begin
        if (RegWrite)
            register_file[write_address] <= write_data;
    end
endmodule

// Register 2 read select multiplexer
module read_mux(output_data, input_data0, input_data1, select);
  parameter word_size = 5;

  // inputs
  input select;
  input [word_size-1:0] input_data0, input_data1;

  // output
  output reg [word_size-1:0] output_data;

  // select the input
  always @(select or input_data0 or input_data1) begin
    case (select)
      0: output_data <= input_data0;
      1: output_data <= input_data1;
      default: output_data <= 0;
    endcase
  end
endmodule

// sign extend module
module sign_extend(input_data, output_data);
  // parameters
  parameter word_size = 32;
  parameter imm_size = 16;

  // inputs and outputs
  input [imm_size-1:0] input_data;
  output [word_size-1:0] output_data;

  // output assignment
  assign output_data = $signed(input_data);
endmodule

// zero extend module
module zero_extend(input_data, output_data);
  // parameters
  parameter word_size = 32;
  parameter imm_size = 16;

  // input and output
  input [imm_size-1:0] input_data;
  output [word_size-1:0] output_data;

  // output assignment
  assign output_data = $unsigned(input_data);
endmodule
