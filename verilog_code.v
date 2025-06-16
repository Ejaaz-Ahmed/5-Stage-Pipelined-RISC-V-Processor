//Ejaz Ahmed, NUM-BSCS-2023-02//
//Pipelined RISC-V Processor with Forwarding and Hazard Detection//

//Program Counter//
module PC(clk, reset, PC_write, PC_IN, PC_OUT);
input clk, reset, PC_write;
input [31:0] PC_IN;
output reg [31:0] PC_OUT;
always @(posedge clk or posedge reset)
begin
if(reset)
PC_OUT <= 32'b00;
else if(PC_write)
PC_OUT <= PC_IN;
end
endmodule

//Program Counter Adder//
module PC_Adder(
    input [31:0] pc_in,
    output [31:0] pc_next
);
    assign pc_next = pc_in + 4;
endmodule

//PC Mux (2x1)//
module PC_Mux(
    input [31:0] pc_next,
    input [31:0] branch_addr,
    input pc_sel,
    output [31:0] pc_out
);
    assign pc_out = (pc_sel) ? branch_addr : pc_next;
endmodule

//Branch Address Adder//
module Branch_Adder(
    input [31:0] pc,
    input [31:0] imm,
    output [31:0] branch_addr
);
    assign branch_addr = pc + imm;
endmodule

//ALU//
module ALU(
 input [31:0] A, B, 
 input [3:0] Control_in, 
 output reg [31:0] Result, 
 output reg zero 
);
always @(*) begin
 case (Control_in)
 4'b0000: Result = A & B;
 4'b0001: Result = A | B;
 4'b0010: Result = A + B;
 4'b0110: Result = A - B;
 4'b0011: Result = ~A; 
 4'b1101: Result = A ^ B; 
 4'b0100: Result = ~(A & B); 
 4'b0111: Result = ~(A | B); 
 4'b1001: Result = A << B; 
 4'b1010: Result = A >> B; 
 4'b1011: Result = $signed(A) >>> B; 
 4'b1000: Result = (A < B) ? 32'd1 : 32'd0; 
 default: Result = 32'b0; 
 endcase
 zero = (Result == 32'b0) ? 1'b1 : 1'b0;
end
endmodule

//ALU Control//
module ALU_control(
 input [6:0] func7,
 input [2:0] func3,
 input [1:0] ALU_op,
 output reg [3:0] ALU_control_out
);
always @(*) 
begin
 case ({ALU_op, func7[5], func3})
 // for R-type Instructions (ALU_op = 2'b10)
 {2'b10, 1'b0, 3'b000}: ALU_control_out = 4'b0010; // ADD
 {2'b10, 1'b1, 3'b000}: ALU_control_out = 4'b0110; // SUB
 {2'b10, 1'b0, 3'b111}: ALU_control_out = 4'b0000; // AND
 {2'b10, 1'b0, 3'b110}: ALU_control_out = 4'b0001; // OR
 {2'b10, 1'b0, 3'b100}: ALU_control_out = 4'b1101; // XOR
 {2'b10, 1'b0, 3'b001}: ALU_control_out = 4'b1001; // SLL
 {2'b10, 1'b0, 3'b101}: ALU_control_out = 4'b1010; // SRL
 {2'b10, 1'b1, 3'b101}: ALU_control_out = 4'b1011; // SRA
 {2'b10, 1'b0, 3'b010}: ALU_control_out = 4'b1000; // SLT
 
 // I-type/Loads/Stores (ALU_op = 2'b00)
 {2'b00, 1'b0, 3'b000}: ALU_control_out = 4'b0010; // ADDI/LW/SW
 
 // Branch (ALU_op = 2'b01)
 {2'b01, 1'b0, 3'b000}: ALU_control_out = 4'b0110; // BEQ
 {2'b01, 1'b0, 3'b001}: ALU_control_out = 4'b0110; // BNE
 
 default: ALU_control_out = 4'b0000;
 endcase
end
endmodule

//Register file//
module Reg_File(
 input clk, 
 input reset, 
 input regwrite, 
 input [4:0] rs1, 
 input [4:0] rs2, 
 input [4:0] rd, 
 input [31:0] writedata, 
 output [31:0] rd1,
 output [31:0] rd2 
);
 reg [31:0] Register [0:31];
 assign rd1 = (rs1 != 0) ? Register[rs1] : 32'b0;
 assign rd2 = (rs2 != 0) ? Register[rs2] : 32'b0;
 integer i;
 always @(posedge clk or posedge reset) 
begin
 if (reset) begin
   for (i = 0; i < 32; i = i + 1) begin
     Register[i] <= 32'b0;
   end
   // Initialize some registers with values for testing
   Register[5] <= 32'd10;
   Register[6] <= 32'd20;
   Register[7] <= 32'd30;
   Register[8] <= 32'd40;
   Register[9] <= 32'd50;
   Register[10] <= 32'd60;
 end
 else if (regwrite && (rd != 0)) begin
   Register[rd] <= writedata;
 end
 end
 
 initial begin
   Register[0] = 32'b0;  // x0 is always 0
 end
endmodule

//Instruction memory//
module instruction_memory(clk, reset, 
address, instruction);
 input clk, reset;
 input [31:0] address;
 output [31:0] instruction;
 reg [31:0] I_mem[1023:0];
 integer i;
 always @(posedge clk)
 begin
 if(reset)
 begin
   for(i=0; i<=1023; i=i+1)
   begin
     I_mem[i] = 32'b0;
   end
   // Sample program for testing pipelining
   I_mem[0] = 32'h00A00513;     // addi x10, x0, 10
   I_mem[4] = 32'h00B00593;     // addi x11, x0, 11
   I_mem[8] = 32'h00C00613;     // addi x12, x0, 12
   I_mem[12] = 32'h00B50533;    // add x10, x10, x11 (data hazard)
   I_mem[16] = 32'h40C58633;    // sub x12, x11, x12
   I_mem[20] = 32'h00A50533;    // add x10, x10, x10 (data hazard)
   I_mem[24] = 32'h00C52023;    // sw x12, 0(x10)
   I_mem[28] = 32'h00052683;    // lw x13, 0(x10) (load-use hazard)
   I_mem[32] = 32'h00D50533;    // add x10, x10, x13 (load-use hazard)
   I_mem[36] = 32'h00068663;    // beq x13, x0, 12 (branch)
 end
 end
 
 assign instruction = I_mem[address];
endmodule

//Data Memory//
module data_memory(clk, reset, mw, mr, 
address, wdata, mout);
 input clk, reset, mr, mw;
 input [31:0] address, wdata;
 output [31:0] mout;
 
 reg [31:0] D_mem[1023:0];
 integer i;
 
 always @(posedge clk)
 begin
 if(reset)
 begin
   for(i=0; i<=1023; i=i+1)
   begin
     D_mem[i] = 32'b0;
   end
   // Initialize some memory locations with values for testing
   D_mem[20] = 32'h000000A;
   D_mem[24] = 32'h000000B;
 end
 else if(mw)
 begin
   D_mem[address] = wdata;
 end
 end
 
 assign mout = mr ? D_mem[address] : 32'b0;
endmodule

//Control//
module control(
 input [6:0] opcode, 
 output reg branch, 
 output reg memread, 
 output reg memtoreg, 
 output reg [1:0] ALUop, 
 output reg memwrite, 
 output reg ALUsource, 
 output reg regW 
);
always @(*) begin
 branch = 1'b0;
 memread = 1'b0;
 memtoreg = 1'b0;
 ALUop = 2'b00;
 memwrite = 1'b0;
 ALUsource = 1'b0;
 regW = 1'b0;
 case (opcode)
 // R-type 
 7'b0110011: begin 
   branch = 1'b0; 
   memread = 1'b0; 
   memtoreg = 1'b0; 
   ALUop = 2'b10;
   memwrite = 1'b0;
   ALUsource = 1'b0; 
   regW = 1'b1; 
 end
 // I-type (arithmetic)
 7'b0010011: begin 
   branch = 1'b0; 
   memread = 1'b0; 
   memtoreg = 1'b0; 
   ALUop = 2'b10;
   memwrite = 1'b0;
   ALUsource = 1'b1; 
   regW = 1'b1; 
 end
 // lw (load word)
 7'b0000011: begin
   branch = 1'b0; 
   memread = 1'b1; 
   memtoreg = 1'b1; 
   ALUop = 2'b00; 
   memwrite = 1'b0;
   ALUsource = 1'b1; 
   regW = 1'b1; 
 end
 // sw (store word)
 7'b0100011: begin
   branch = 1'b0; 
   memread = 1'b0; 
   memtoreg = 1'bx; 
   ALUop = 2'b00; 
   memwrite = 1'b1; 
   ALUsource = 1'b1; 
   regW = 1'b0; 
 end
 // SB-Type means branch instructions
 7'b1100011: begin
   branch = 1'b1;  // Enable branch
   memread = 1'b0; 
   memtoreg = 1'bx; 
   ALUop = 2'b01; 
   memwrite = 1'b0; 
   ALUsource = 1'b0;
   regW = 1'b0; 
 end
 // Default case
 default: begin
   branch = 1'b0;
   memread = 1'b0;
   memtoreg = 1'b0;
   ALUop = 2'b00;
   memwrite = 1'b0;
   ALUsource = 1'b0;
   regW = 1'b0;
 end
 endcase
end
endmodule

//Immediate Generator//
module immediate_generator(
    input [31:0] instruction,    
    output reg [31:0] imm_out   
);

    always @(*) begin
        case (instruction[6:0]) 
            // I-type 
            7'b0010011: imm_out = {{20{instruction[31]}}, instruction[31:20]};  

            // Load-type 
            7'b0000011: imm_out = {{20{instruction[31]}}, instruction[31:20]};  

            // S-type 
            7'b0100011: imm_out = {{20{instruction[31]}}, instruction[31:25], instruction[11:7]};  

            // SB-type (means branch)
            7'b1100011: imm_out = {{19{instruction[31]}}, instruction[7], instruction[30:25], instruction[11:8], 1'b0};   

            default: imm_out = 32'b0;
        endcase
    end

endmodule

// ALU Source Mux (2x1)
module ALU_Mux(
    input [31:0] rd2,
    input [31:0] imm,
    input ALUsource,
    output [31:0] ALU_B
);
    assign ALU_B = ALUsource ? imm : rd2;
endmodule

// Data Memory to Register Write Back Mux (2x1)
module WB_Mux(
    input [31:0] ALU_result,
    input [31:0] mem_data,
    input memtoreg,
    output [31:0] writedata
);
    assign writedata = memtoreg ? mem_data : ALU_result;
endmodule

// Forwarding Mux A (3x1)
module Forward_Mux_A(
    input [31:0] rs1_data,
    input [31:0] wb_data,
    input [31:0] mem_data,
    input [1:0] forwardA,
    output [31:0] alu_src_a
);
    assign alu_src_a = (forwardA == 2'b10) ? mem_data :
                       (forwardA == 2'b01) ? wb_data : rs1_data;
endmodule

// Forwarding Mux B (3x1)
module Forward_Mux_B(
    input [31:0] alu_b,
    input [31:0] wb_data,
    input [31:0] mem_data,
    input [1:0] forwardB,
    output [31:0] alu_src_b
);
    assign alu_src_b = (forwardB == 2'b10) ? mem_data :
                       (forwardB == 2'b01) ? wb_data : alu_b;
endmodule

// Control Mux for Hazard Detection
module Control_Mux(
    input branch, memread, memtoreg, memwrite, ALUsource, regW,
    input [1:0] ALUop,
    input control_mux_select,
    output reg out_branch, out_memread, out_memtoreg, out_memwrite, out_ALUsource, out_regW,
    output reg [1:0] out_ALUop
);
    always @(*) begin
        if (control_mux_select) begin
            // Insert NOP (bubble)
            out_branch = 1'b0;
            out_memread = 1'b0;
            out_memtoreg = 1'b0;
            out_memwrite = 1'b0;
            out_ALUsource = 1'b0;
            out_regW = 1'b0;
            out_ALUop = 2'b00;
        end else begin
            out_branch = branch;
            out_memread = memread;
            out_memtoreg = memtoreg;
            out_memwrite = memwrite;
            out_ALUsource = ALUsource;
            out_regW = regW;
            out_ALUop = ALUop;
        end
    end
endmodule

// Pipeline Registers
module IF_ID_Register (
input clk,
input reset,
input IF_ID_write,
input [31:0] IF_PC,
input [31:0] IF_Instr,
output reg [31:0] ID_PC,
output reg [31:0] ID_Instr
);
always @(posedge clk or posedge reset) begin
if (reset) begin
ID_PC <= 32'b0;
ID_Instr <= 32'b0;
end
else if (IF_ID_write) begin
ID_PC <= IF_PC;
ID_Instr <= IF_Instr;
end
end
endmodule

module ID_EXE_Register (
input clk,
input reset,
input [31:0] ID_PC,
input [31:0] ID_ReadData1,
input [31:0] ID_ReadData2,
input [31:0] ID_Imm,
input [4:0] ID_Rd,
input [4:0] ID_Rs1,
input [4:0] ID_Rs2,
input ID_RegWrite,
input ID_MemRead,
input ID_MemWrite,
input ID_Branch,
input [1:0] ID_ALUOp,
input ID_ALUSrc,
input ID_MemToReg,
output reg [31:0] EXE_PC,
output reg [31:0] EXE_ReadData1,
output reg [31:0] EXE_ReadData2,
output reg [31:0] EXE_Imm,
output reg [4:0] EXE_Rd,
output reg [4:0] EXE_Rs1,
output reg [4:0] EXE_Rs2,
output reg EXE_RegWrite,
output reg EXE_MemRead,
output reg EXE_MemWrite,
output reg EXE_Branch,
output reg [1:0] EXE_ALUOp,
output reg EXE_ALUSrc,
output reg EXE_MemToReg
);
always @(posedge clk or posedge reset) begin
if (reset) begin
EXE_PC <= 32'b0;
EXE_ReadData1 <= 32'b0;
EXE_ReadData2 <= 32'b0;
EXE_Imm <= 32'b0;
EXE_Rd <= 5'b0;
EXE_Rs1 <= 5'b0;
EXE_Rs2 <= 5'b0;
EXE_RegWrite <= 0;
EXE_MemRead <= 0;
EXE_MemWrite <= 0;
EXE_Branch <= 0;
EXE_ALUOp <= 2'b00;
EXE_ALUSrc <= 0;
EXE_MemToReg <= 0;
end
else begin
EXE_PC <= ID_PC;
EXE_ReadData1 <= ID_ReadData1;
EXE_ReadData2 <= ID_ReadData2;
EXE_Imm <= ID_Imm;
EXE_Rd <= ID_Rd;
EXE_Rs1 <= ID_Rs1;
EXE_Rs2 <= ID_Rs2;
EXE_RegWrite <= ID_RegWrite;
EXE_MemRead <= ID_MemRead;
EXE_MemWrite <= ID_MemWrite;
EXE_Branch <= ID_Branch;
EXE_ALUOp <= ID_ALUOp;
EXE_ALUSrc <= ID_ALUSrc;
EXE_MemToReg <= ID_MemToReg;
end
end
endmodule

module exe_mem_Register (
input clk,
input reset,
input MemRead_in,
input MemWrite_in,
input MemtoReg_in,
input RegWrite_in,
input [31:0] ALU_result_in,
input [31:0] WriteData_in,
input [4:0] Rd_in,
input zero_in,
input [31:0] BranchAddr_in,
input Branch_in,
output reg MemRead_out,
output reg MemWrite_out,
output reg MemtoReg_out,
output reg RegWrite_out,
output reg [31:0] ALU_result_out,
output reg [31:0] WriteData_out,
output reg [4:0] Rd_out,
output reg zero_out,
output reg [31:0] BranchAddr_out,
output reg Branch_out
);
always @(posedge clk or posedge reset) begin
if (reset) begin
MemRead_out <= 0;
MemWrite_out <= 0;
MemtoReg_out <= 0;
RegWrite_out <= 0;
ALU_result_out <= 0;
WriteData_out <= 0;
Rd_out <= 0;
zero_out <= 0;
BranchAddr_out <= 0;
Branch_out <= 0;
end else begin
MemRead_out <= MemRead_in;
MemWrite_out <= MemWrite_in;
MemtoReg_out <= MemtoReg_in;
RegWrite_out <= RegWrite_in;
ALU_result_out <= ALU_result_in;
WriteData_out <= WriteData_in;
Rd_out <= Rd_in;
zero_out <= zero_in;
BranchAddr_out <= BranchAddr_in;
Branch_out <= Branch_in;
end
end
endmodule

module mem_wb_register (
input clk, rst, regwrite_mem, MemToReg_mem,
input [31:0] ALU_result_mem, read_data_mem,
input [4:0] rd_mem,
output reg regwrite_wb, MemToReg_wb,
output reg [31:0] ALU_result_wb, read_data_wb,
output reg [4:0] rd_wb
);
always @(posedge clk or posedge rst) begin
if (rst) begin
regwrite_wb <= 1'b0;
MemToReg_wb <= 1'b0;
ALU_result_wb <= 32'b0;
read_data_wb <= 32'b0;
rd_wb <= 5'b0;
end
else begin
regwrite_wb <= regwrite_mem;
MemToReg_wb <= MemToReg_mem;
ALU_result_wb <= ALU_result_mem;
read_data_wb <= read_data_mem;
rd_wb <= rd_mem;
end
end
endmodule

module forwarding_unit(
input [4:0] EX_rs1, EX_rs2,
input [4:0] MEM_rd, WB_rd,
input MEM_regwrite, WB_regwrite,
output reg [1:0] forwardA, forwardB
);
always @(*)
begin
forwardA = 2'b00;
forwardB = 2'b00;
if (MEM_regwrite && (MEM_rd != 0) && (MEM_rd == EX_rs1))
forwardA = 2'b10;
if (MEM_regwrite && (MEM_rd != 0) && (MEM_rd == EX_rs2))
forwardB = 2'b10;
if (WB_regwrite && (WB_rd != 0) &&
!(MEM_regwrite && (MEM_rd != 0) && (MEM_rd == EX_rs1)) &&
(WB_rd == EX_rs1))
forwardA = 2'b01;
if (WB_regwrite && (WB_rd != 0) &&
!(MEM_regwrite && (MEM_rd != 0) && (MEM_rd == EX_rs2)) &&
(WB_rd == EX_rs2))
forwardB = 2'b01;
end
endmodule

module hazard_detection(
input [4:0] ID_rs1, ID_rs2,
input [4:0] EX_rd,
input EX_memread,
output reg PC_write,
output reg IF_ID_write,
output reg control_mux_select
);
always @(*)
begin
PC_write = 1'b1;
IF_ID_write = 1'b1;
control_mux_select = 1'b0;
if (EX_memread && ((EX_rd == ID_rs1) || (EX_rd == ID_rs2)))
begin
PC_write = 1'b0;
IF_ID_write = 1'b0;
control_mux_select = 1'b1;
end
end
endmodule

//Pipelined RISC-V Top Module//
module Pipelined_Riscv_top(
	input clk, reset
);

// IF Stage Wires
wire [31:0] IF_PC, IF_PC_next, IF_instruction;
wire [31:0] branch_addr;
wire pc_sel, PC_write;

// ID Stage Wires  
wire [31:0] ID_PC, ID_instruction;
wire [31:0] ID_RD1, ID_RD2, ID_imm;
wire [4:0] ID_rs1, ID_rs2, ID_rd;
wire ID_branch, ID_memread, ID_memtoreg, ID_memwrite, ID_ALUsource, ID_regW;
wire [1:0] ID_ALUop;
wire IF_ID_write, control_mux_select;

// ID Control signals after hazard mux
wire ID_branch_mux, ID_memread_mux, ID_memtoreg_mux, ID_memwrite_mux, ID_ALUsource_mux, ID_regW_mux;
wire [1:0] ID_ALUop_mux;

// EX Stage Wires
wire [31:0] EX_PC, EX_RD1, EX_RD2, EX_imm;
wire [4:0] EX_rs1, EX_rs2, EX_rd;
wire EX_branch, EX_memread, EX_memtoreg, EX_memwrite, EX_ALUsource, EX_regW;
wire [1:0] EX_ALUop;
wire [31:0] EX_ALU_A, EX_ALU_B, EX_ALU_result;
wire [31:0] EX_forward_A, EX_forward_B;
wire [3:0] EX_ALU_control;
wire EX_zero;
wire [1:0] forwardA, forwardB;

// MEM Stage Wires
wire [31:0] MEM_ALU_result, MEM_WriteData, MEM_branch_addr;
wire [4:0] MEM_rd;
wire MEM_memread, MEM_memwrite, MEM_memtoreg, MEM_regW, MEM_zero, MEM_branch;
wire [31:0] MEM_mem_data;

// WB Stage Wires
wire [31:0] WB_ALU_result, WB_mem_data, WB_writedata;
wire [4:0] WB_rd;
wire WB_regW, WB_memtoreg;

// Extract instruction fields
assign ID_rs1 = ID_instruction[19:15];
assign ID_rs2 = ID_instruction[24:20];
assign ID_rd = ID_instruction[11:7];

// Branch control
assign pc_sel = MEM_branch & MEM_zero;

// IF Stage
PC program_counter(
    .clk(clk), 
    .reset(reset), 
    .PC_write(PC_write),
    .PC_IN(pc_sel ? MEM_branch_addr : IF_PC_next), 
    .PC_OUT(IF_PC)
);

PC_Adder pc_adder(
    .pc_in(IF_PC),
    .pc_next(IF_PC_next)
);

instruction_memory instr_mem(
    .clk(clk),
    .reset(reset),
    .address(IF_PC),
    .instruction(IF_instruction)
);

// IF/ID Pipeline Register
IF_ID_Register if_id_reg(
    .clk(clk),
    .reset(reset),
    .IF_ID_write(IF_ID_write),
    .IF_PC(IF_PC),
    .IF_Instr(IF_instruction),
    .ID_PC(ID_PC),
    .ID_Instr(ID_instruction)
);

// ID Stage
control control_unit(
    .opcode(ID_instruction[6:0]),
    .branch(ID_branch),
    .memread(ID_memread),
    .memtoreg(ID_memtoreg),
    .ALUop(ID_ALUop),
    .memwrite(ID_memwrite),
    .ALUsource(ID_ALUsource),
    .regW(ID_regW)
);

// Hazard Detection Unit
hazard_detection hazard_unit(
    .ID_rs1(ID_rs1),
    .ID_rs2(ID_rs2),
    .EX_rd(EX_rd),
    .EX_memread(EX_memread),
    .PC_write(PC_write),
    .IF_ID_write(IF_ID_write),
    .control_mux_select(control_mux_select)
);

// Control Hazard Mux
Control_Mux control_mux(
    .branch(ID_branch),
    .memread(ID_memread),
    .memtoreg(ID_memtoreg),
    .memwrite(ID_memwrite),
    .ALUsource(ID_ALUsource),
    .regW(ID_regW),
    .ALUop(ID_ALUop),
    .control_mux_select(control_mux_select),
    .out_branch(ID_branch_mux),
    .out_memread(ID_memread_mux),
    .out_memtoreg(ID_memtoreg_mux),
    .out_memwrite(ID_memwrite_mux),
    .out_ALUsource(ID_ALUsource_mux),
    .out_regW(ID_regW_mux),
    .out_ALUop(ID_ALUop_mux)
);

Reg_File register_file(
    .clk(clk),
    .reset(reset),
    .regwrite(WB_regW),
    .rs1(ID_rs1),
    .rs2(ID_rs2),
    .rd(WB_rd),
    .writedata(WB_writedata),
    .rd1(ID_RD1),
    .rd2(ID_RD2)
);

immediate_generator imm_gen(
    .instruction(ID_instruction),
    .imm_out(ID_imm)
);

// ID/EX Pipeline Register
ID_EXE_Register id_ex_reg(
    .clk(clk),
    .reset(reset),
    .ID_PC(ID_PC),
    .ID_ReadData1(ID_RD1),
    .ID_ReadData2(ID_RD2),
    .ID_Imm(ID_imm),
    .ID_Rd(ID_rd),
    .ID_Rs1(ID_rs1),
    .ID_Rs2(ID_rs2),
    .ID_RegWrite(ID_regW_mux),
    .ID_MemRead(ID_memread_mux),
    .ID_MemWrite(ID_memwrite_mux),
    .ID_Branch(ID_branch_mux),
    .ID_ALUOp(ID_ALUop_mux),
    .ID_ALUSrc(ID_ALUsource_mux),
    .ID_MemToReg(ID_memtoreg_mux),
    .EXE_PC(EX_PC),
    .EXE_ReadData1(EX_RD1),
    .EXE_ReadData2(EX_RD2),
    .EXE_Imm(EX_imm),
    .EXE_Rd(EX_rd),
    .EXE_Rs1(EX_rs1),
    .EXE_Rs2(EX_rs2),
    .EXE_RegWrite(EX_regW),
    .EXE_MemRead(EX_memread),
    .EXE_MemWrite(EX_memwrite),
    .EXE_Branch(EX_branch),
    .EXE_ALUOp(EX_ALUop),
    .EXE_ALUSrc(EX_ALUsource),
    .EXE_MemToReg(EX_memtoreg)
);

// EX Stage
// Forwarding Unit
forwarding_unit forward_unit(
    .EX_rs1(EX_rs1),
    .EX_rs2(EX_rs2),
    .MEM_rd(MEM_rd),
    .WB_rd(WB_rd),
    .MEM_regwrite(MEM_regW),
    .WB_regwrite(WB_regW),
    .forwardA(forwardA),
    .forwardB(forwardB)
);

// Forward Mux A
Forward_Mux_A forward_mux_a(
    .rs1_data(EX_RD1),
    .wb_data(WB_writedata),
    .mem_data(MEM_ALU_result),
    .forwardA(forwardA),
    .alu_src_a(EX_forward_A)
);

// ALU Source Mux
ALU_Mux alu_src_mux(
    .rd2(EX_RD2),
    .imm(EX_imm),
    .ALUsource(EX_ALUsource),
    .ALU_B(EX_ALU_B)
);

// Forward Mux B
Forward_Mux_B forward_mux_b(
    .alu_b(EX_ALU_B),
    .wb_data(WB_writedata),
    .mem_data(MEM_ALU_result),
    .forwardB(forwardB),
    .alu_src_b(EX_forward_B)
);

// ALU Control
ALU_control alu_control(
    .func7(EX_imm[31:25]), // Use immediate field for func7
    .func3(EX_imm[14:12]), // Use immediate field for func3
    .ALU_op(EX_ALUop),
    .ALU_control_out(EX_ALU_control)
);

// ALU
ALU alu(
    .A(EX_forward_A),
    .B(EX_forward_B),
    .Control_in(EX_ALU_control),
    .Result(EX_ALU_result),
    .zero(EX_zero)
);

// Branch Address Calculation
Branch_Adder branch_adder(
    .pc(EX_PC),
    .imm(EX_imm),
    .branch_addr(branch_addr)
);

// EX/MEM Pipeline Register
exe_mem_Register ex_mem_reg(
    .clk(clk),
    .reset(reset),
    .MemRead_in(EX_memread),
    .MemWrite_in(EX_memwrite),
    .MemtoReg_in(EX_memtoreg),
    .RegWrite_in(EX_regW),
    .ALU_result_in(EX_ALU_result),
    .WriteData_in(EX_forward_B),
    .Rd_in(EX_rd),
    .zero_in(EX_zero),
    .BranchAddr_in(branch_addr),
    .Branch_in(EX_branch),
    .MemRead_out(MEM_memread),
    .MemWrite_out(MEM_memwrite),
    .MemtoReg_out(MEM_memtoreg),
    .RegWrite_out(MEM_regW),
    .ALU_result_out(MEM_ALU_result),
    .WriteData_out(MEM_WriteData),
    .Rd_out(MEM_rd),
    .zero_out(MEM_zero),
    .BranchAddr_out(MEM_branch_addr),
    .Branch_out(MEM_branch)
);

// MEM Stage
data_memory data_mem(
    .clk(clk),
    .reset(reset),
    .mw(MEM_memwrite),
    .mr(MEM_memread),
    .address(MEM_ALU_result),
    .wdata(MEM_WriteData),
    .mout(MEM_mem_data)
);

// MEM/WB Pipeline Register
mem_wb_register mem_wb_reg(
    .clk(clk),
    .rst(reset),
    .regwrite_mem(MEM_regW),
    .MemToReg_mem(MEM_memtoreg),
    .ALU_result_mem(MEM_ALU_result),
    .read_data_mem(MEM_mem_data),
    .rd_mem(MEM_rd),
    .regwrite_wb(WB_regW),
    .MemToReg_wb(WB_memtoreg),
    .ALU_result_wb(WB_ALU_result),
    .read_data_wb(WB_mem_data),
    .rd_wb(WB_rd)
);

// WB Stage
WB_Mux wb_mux(
    .ALU_result(WB_ALU_result),
    .mem_data(WB_mem_data),
    .memtoreg(WB_memtoreg),
    .writedata(WB_writedata)
);

endmodule

//=====================Pipelined RISC-V Testbench//
module Pipelined_Riscv_top_tb;

// Testbench signals
reg clk, reset;

// Instantiate the Pipelined RISC-V processor
Pipelined_Riscv_top dut(
    .clk(clk),
    .reset(reset)
);

// Clock generation
initial begin
    clk = 0;
    forever #5 clk = ~clk; // 10ns period clock
end

// Monitor for Pipeline Stages
initial begin
    $display("=== Pipelined RISC-V Processor Simulation ===");
    $display("Time | PC   | IF_Instr | ID_Instr | EX_ALU | MEM_Data | WB_Data | Hazard | Forward");
    $display("-----|------|----------|----------|--------|----------|---------|---------|--------");
    
    $monitor("%4t | %4h | %8h | %8h | %6h | %8h | %7h | %1b,%1b,%1b | %1d,%1d", 
             $time, 
             dut.IF_PC[7:0], 
             dut.IF_instruction, 
             dut.ID_instruction, 
             dut.EX_ALU_result[15:0], 
             dut.MEM_mem_data[15:0], 
             dut.WB_writedata[15:0],
             dut.PC_write,
             dut.IF_ID_write, 
             dut.control_mux_select,
             dut.forwardA,
             dut.forwardB);
end

// Additional monitors for detailed pipeline analysis
initial begin
    $display("\n=== Pipeline Stage Contents ===");
end

always @(posedge clk) begin
    if (!reset) begin
        $display("\n--- Cycle %0d ---", ($time-20)/10);
        $display("IF:  PC=%h, Instr=%h", dut.IF_PC, dut.IF_instruction);
        $display("ID:  PC=%h, Instr=%h, rs1=%d, rs2=%d, rd=%d", 
                 dut.ID_PC, dut.ID_instruction, dut.ID_rs1, dut.ID_rs2, dut.ID_rd);
        $display("EX:  rs1=%d, rs2=%d, rd=%d, ALU=%h, forwardA=%d, forwardB=%d", 
                 dut.EX_rs1, dut.EX_rs2, dut.EX_rd, dut.EX_ALU_result, dut.forwardA, dut.forwardB);
        $display("MEM: rd=%d, ALU=%h, MemData=%h, RegWrite=%b", 
                 dut.MEM_rd, dut.MEM_ALU_result, dut.MEM_mem_data, dut.MEM_regW);
        $display("WB:  rd=%d, WriteData=%h, RegWrite=%b", 
                 dut.WB_rd, dut.WB_writedata, dut.WB_regW);
        
        // Hazard Detection Status
        if (dut.control_mux_select)
            $display("*** LOAD-USE HAZARD DETECTED - PIPELINE STALLED ***");
        if (dut.forwardA != 2'b00 || dut.forwardB != 2'b00)
            $display("*** DATA FORWARDING ACTIVE: ForwardA=%d, ForwardB=%d ***", dut.forwardA, dut.forwardB);
        if (dut.pc_sel)
            $display("*** BRANCH TAKEN ***");
    end
end

// Register file monitoring
initial begin
    #25; // Wait for reset to complete
    $display("\n=== Register File Changes ===");
end

always @(posedge clk) begin
    if (!reset && dut.WB_regW && dut.WB_rd != 0) begin
        $display("Time %4t: Register x%0d updated to %h", $time, dut.WB_rd, dut.WB_writedata);
    end
end

// Performance metrics
integer cycle_count;
integer instruction_count;
integer hazard_count;
integer forward_count;

initial begin
    cycle_count = 0;
    instruction_count = 0;
    hazard_count = 0;
    forward_count = 0;
end

always @(posedge clk) begin
    if (!reset) begin
        cycle_count = cycle_count + 1;
        
        // Count instructions (when they complete WB stage)
        if (dut.WB_regW || dut.mem_wb_reg.MemToReg_wb) begin
            instruction_count = instruction_count + 1;
        end
        
        // Count hazards
        if (dut.control_mux_select) begin
            hazard_count = hazard_count + 1;
        end
        
        // Count forwarding events
        if (dut.forwardA != 2'b00 || dut.forwardB != 2'b00) begin
            forward_count = forward_count + 1;
        end
    end
end

// Test sequence
initial begin
    // Apply reset
    reset = 1;
    #20;
    reset = 0;
    
    $display("\n=== Starting Pipeline Execution ===");
    
    // Run for sufficient cycles to see pipeline effects
    #500;
    
    // Display performance metrics
    $display("\n=== Performance Metrics ===");
    $display("Total Cycles: %0d", cycle_count);
    $display("Instructions Completed: %0d", instruction_count);
    $display("Hazard Stalls: %0d", hazard_count);
    $display("Forwarding Events: %0d", forward_count);
    
   if (cycle_count > 0) begin
    $display("CPI (Cycles Per Instruction): %d.%02d", 
             (cycle_count * 100) / instruction_count, 
             (cycle_count * 100) % instruction_count);
    end
    // End simulation
    $finish;
end

endmodule
