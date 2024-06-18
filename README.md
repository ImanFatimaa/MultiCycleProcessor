# MultiCycleProcessor

The provided Verilog code segments are designed to create a multi-cycle CPU architecture. The architecture consists of several key modules:

The MultiCycleCPU module serves as the top-level entity that connects the datapath and controller modules. It manages signals such as clock (clk) and reset (reset) and facilitates the exchange of control signals between the datapath and controller.

Within the controller module, the control logic is implemented to determine the appropriate control signals based on the opcode received. These signals dictate the flow and operation of the CPU during different stages of instruction execution.

The datapath module contains the core components of the CPU's data path. This includes registers such as the Program Counter (PC), Instruction Register (IR), and general-purpose registers (A, B). It also incorporates components like the Arithmetic Logic Unit (ALU) for performing arithmetic and logical operations, as well as multiplexers (muxes) for selecting inputs.

Additionally, the datapath module includes interfaces to Instruction Memory (IMem) and Data Memory (DMem) for storing instructions and data, respectively. These memories are crucial for reading instructions to be executed and storing or retrieving data during program execution.

Overall, the Verilog code segments collectively simulate the behavior of a multi-cycle CPU architecture, demonstrating how instructions are fetched, decoded, executed, and data is manipulated within the hardware components of the CPU. This design can be utilized for educational purposes to understand digital logic and computer architecture fundamentals, or as a basis for developing more sophisticated CPU designs.
