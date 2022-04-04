`ifndef AXI4_SLAVE_AGENT_CONFIG_INCLUDED_
`define AXI4_SLAVE_AGENT_CONFIG_INCLUDED_

//--------------------------------------------------------------------------------------------
// Class: axi4_slave_agent_config
// Used as the configuration class for axi4_slave agent and it's components
//--------------------------------------------------------------------------------------------
class axi4_slave_agent_config extends uvm_object;
  `uvm_object_utils(axi4_slave_agent_config)

  //Variable: is_active
  //Used for creating the agent in either passive or active mode
  uvm_active_passive_enum is_active = UVM_ACTIVE;  
  
  //Variable: has_coverage
  //Used for enabling the master agent coverage
  bit has_coverage;

  //Variable: slave_id
  //Gives the slave id
  int slave_id;
  
  //Variable : max_address
  //Used to store the maximum address value of this slave
  bit [ADDRESS_WIDTH-1:0] max_address;

  //Variable : min_address
  //Used to store the minimum address value of this slave
  bit [ADDRESS_WIDTH-1:0] min_address;
  
  //Variable : slave_memory
  //Declaration of slave_memory to store the data from master
  bit [7:0] slave_memory [longint];
  
  //Variable : wait_count_write_response_channel;
  //Used to determine the number of wait states inserted for write response channel
  int wait_count_write_response_channel;
  
  //Variable : wait_count_read_data_channel;
  //Used to determine the number of wait states inserted for read data channel
  int wait_count_read_data_channel;

  //-------------------------------------------------------
  // Externally defined Tasks and Functions
  //-------------------------------------------------------
  extern function new(string name = "axi4_slave_agent_config");
  extern function void do_print(uvm_printer printer);
  extern virtual task slave_memory_task(bit [ADDRESS_WIDTH-1:0]slave_address, bit [DATA_WIDTH-1:0]data);
endclass : axi4_slave_agent_config

//--------------------------------------------------------------------------------------------
// Construct: new
//
// Parameters:
//  name - axi4_slave_agent_config
//--------------------------------------------------------------------------------------------
function axi4_slave_agent_config::new(string name = "axi4_slave_agent_config");
  super.new(name); 
endfunction : new

//--------------------------------------------------------------------------------------------
//Task : slave_memory_task
//Used to store the slave data into the slave memory
//Parameter :
//slave_address - bit [ADDRESS_WIDTH-1 :0]
//data          - bit [DATA_WIDTH-1:0]
//--------------------------------------------------------------------------------------------
task axi4_slave_agent_config::slave_memory_task(bit [ADDRESS_WIDTH-1 :0]slave_address, bit [DATA_WIDTH-1:0]data);
  slave_memory[slave_address] = data;
endtask : slave_memory_task

//--------------------------------------------------------------------------------------------
// Function: do_print method
// Print method can be added to display the data members values
//
// Parameters:
//  printer - uvm_printer
//--------------------------------------------------------------------------------------------
function void axi4_slave_agent_config::do_print(uvm_printer printer);
  super.do_print(printer);

  printer.print_string ("is_active",   is_active.name());
  printer.print_field ("slave_id",     slave_id,     $bits(slave_id),     UVM_DEC);
  printer.print_field ("has_coverage", has_coverage, $bits(has_coverage), UVM_DEC);
  printer.print_field ("min_address",  min_address,  $bits(max_address),  UVM_HEX);
  printer.print_field ("max_address",  max_address,  $bits(max_address),  UVM_HEX);
  printer.print_field ("wait_count_write_response_channel",wait_count_write_response_channel,$bits(wait_count_write_response_channel),UVM_DEC);
  printer.print_field ("wait_count_read_data_channel",wait_count_read_data_channel,$bits(wait_count_read_data_channel),UVM_DEC);
         
endfunction : do_print

`endif

