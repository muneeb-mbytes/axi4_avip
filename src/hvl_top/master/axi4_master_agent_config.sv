`ifndef AXI4_MASTER_AGENT_CONFIG_INCLUDED_
`define AXI4_MASTER_AGENT_CONFIG_INCLUDED_

//--------------------------------------------------------------------------------------------
// Class: axi4_master_agent_config
// Used as the configuration class for axi4_master agent, for configuring number of slaves and number
// of active passive agents to be created
//--------------------------------------------------------------------------------------------
class axi4_master_agent_config extends uvm_object;
  `uvm_object_utils(axi4_master_agent_config)

  // Variable: is_active
  // Used for creating the agent in either passive or active mode
  uvm_active_passive_enum is_active=UVM_ACTIVE;  

  // Variable: no_of_masters
  // Used for specifying the number of masters connected to this axi4_master over axi4 interface
  int no_of_masters;

  // Variable: no_of_slaves
  // Used for specifying the number of slaves connected to this axi4_master over axi4 interface
  int no_of_slaves;
  
  // Variable: has_coverage
  // Used for enabling the master agent coverage
  bit has_coverage;


  //Variable: slave_no
  //Used to indicate the slave number
  //slave_no_e slave_no;
  
  //Variable : master_memory
  //Used to store all the data from the slaves
  //Each location of the master memory stores 32 bit data
  bit [MEMORY_WIDTH-1:0]master_memory[(SLAVE_MEMORY_SIZE+SLAVE_MEMORY_GAP)*NO_OF_SLAVES:0];

  //Variable : master_min_array
  //An associative array used to store the min address ranges of every slave
  //Index - type    - int
  //        stores  - slave number
  //Value - stores the minimum address range of that slave.
  bit [AXI_AW-1:0]master_min_addr_range_array[int];

  //Variable : master_max_array
  //An associative array used to store the max address ranges of every slave
  //Index - type    - int
  //        stores  - slave number
  //Value - stores the maximum address range of that slave.
  bit [AXI_AW-1:0]master_max_addr_range_array[int];
  


  //-------------------------------------------------------
  // Externally defined Tasks and Functions
  //-------------------------------------------------------
  extern function new(string name = "axi4_master_agent_config");
  extern function void master_min_addr_range(int slave_number, bit [AXI_AW-1:0]slave_min_address_range);
  extern function void master_max_addr_range(int slave_number, bit [AXI_AW-1:0]slave_max_address_range);
endclass : axi4_master_agent_config

//--------------------------------------------------------------------------------------------
// Construct: new
//
// Parameters:
//  name - axi4_master_agent_config
//--------------------------------------------------------------------------------------------
function axi4_master_agent_config::new(string name = "axi4_master_agent_config");
  super.new(name);
endfunction : new


//--------------------------------------------------------------------------------------------
// Function : master_max_addr_range_array
// Used to store the maximum address ranges of the slaves in the array
// Parameters :
//  slave_number            - int
//  slave_max_address_range - bit [63:0]
//--------------------------------------------------------------------------------------------
function void axi4_master_agent_config::master_max_addr_range(int slave_number, bit[AXI_AW-1:0]slave_max_address_range);
  master_max_addr_range_array[slave_number] = slave_max_address_range;
endfunction : master_max_addr_range

//--------------------------------------------------------------------------------------------
// Function : master_min_addr_range_array
// Used to store the minimum address ranges of the slaves in the array
// Parameters :
//  slave_number            - int
//  slave_min_address_range - bit [63:0]
//--------------------------------------------------------------------------------------------
function void axi4_master_agent_config::master_min_addr_range(int slave_number, bit[AXI_AW-1:0]slave_min_address_range);
  master_min_addr_range_array[slave_number] = slave_min_address_range;
endfunction : master_min_addr_range


`endif

