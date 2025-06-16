# 5-Stage-Pipelined-RISC-V-Processor
## 🛠️ Implementation Details

### 🔑 Key Components

The processor is implemented in **Verilog** and consists of several major components:

- **Program Counter (PC) and Instruction Memory**  
  The PC tracks the current instruction address, while the instruction memory stores the program code.

- **Register File**  
  A 32-register file (with `x0` hardwired to zero) provides operand storage and supports simultaneous read/write operations.

- **Arithmetic Logic Unit (ALU)**  
  The ALU performs arithmetic, logical, and shift operations based on control signals from the ALU Control unit.

- **Data Memory**  
  A synchronous memory module handles load and store operations.

- **Control Unit**  
  Generates pipeline control signals (e.g., `RegWrite`, `MemRead`, `Branch`) based on the instruction opcode.

- **Forwarding and Hazard Units**  
  Detect dependencies and manage forwarding or stalling to ensure correct execution.

---

### ⛓️ Pipeline Registers

Each pipeline stage is separated by registers that propagate control signals and intermediate results:

- **IF/ID Register**  
  Holds the fetched instruction and PC value for the Decode stage.

- **ID/EX Register**  
  Passes decoded operands, control signals, and immediate values to the Execute stage.

- **EX/MEM Register**  
  Stores ALU results, memory access signals, and branch information.

- **MEM/WB Register**  
  Buffers data memory results and write-back information for the register file.

These registers ensure that each stage operates on the correct data and control signals, even as multiple instructions progress through the pipeline simultaneously.
