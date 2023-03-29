`ifndef AXI4_SLAVE_MEMORY_INCLUDED_
`define AXI4_SLAVE_MEMORY_INCLUDED_

//--------------------------------------------------------------------------------------------
// Class: axi4_slave_agent
// This agent has sequencer, driver_proxy, monitor_proxy for axi4  
//--------------------------------------------------------------------------------------------
class axi4_slave_memory extends uvm_object;
  `uvm_object_utils(axi4_slave_memory)

  //Variable : slave_memory
  //Declaration of slave_memory to store the data from master
  protected bit [7:0] slave_memory [longint];

  extern function new(string name = "axi4_slave_memory");  
  extern virtual function void mem_write(input bit [ADDRESS_WIDTH-1:0]slave_address, bit [DATA_WIDTH-1:0]data);
  extern virtual function void mem_read (input bit [ADDRESS_WIDTH-1:0]slave_address, output bit [DATA_WIDTH-1:0]data);
  extern virtual function bit is_slave_addr_exists(input bit [ADDRESS_WIDTH-1 :0]slave_address);

endclass : axi4_slave_memory

//--------------------------------------------------------------------------------------------
// Construct: new
//
// Parameters:
//  name - axi4_slave_agent_config
//--------------------------------------------------------------------------------------------
function axi4_slave_memory::new(string name = "axi4_slave_memory");
  super.new(name); 
endfunction : new


//--------------------------------------------------------------------------------------------
//Task : slave_memory_task
//Used to store the slave data into the slave memory
//Parameter :
//slave_address - bit [ADDRESS_WIDTH-1 :0]
//data          - bit [DATA_WIDTH-1:0]
//--------------------------------------------------------------------------------------------
function void axi4_slave_memory::mem_write(input bit [ADDRESS_WIDTH-1 :0]slave_address, bit [DATA_WIDTH-1:0]data);
  slave_memory[slave_address] = data;
   $display("WR_MEM addr:%0h, data:%0h",slave_address,slave_memory[slave_address]);
endfunction : mem_write

function void axi4_slave_memory::mem_read(input bit [ADDRESS_WIDTH-1 :0]slave_address, output bit [DATA_WIDTH-1:0]data);
   data = slave_memory[slave_address];
   $display("RD_MEM addr:%0h, data:%0h",slave_address,data);
endfunction : mem_read

function bit axi4_slave_memory::is_slave_addr_exists(input bit [ADDRESS_WIDTH-1 :0]slave_address);
  is_slave_addr_exists = slave_memory.exists(slave_address);
endfunction: is_slave_addr_exists


`endif
