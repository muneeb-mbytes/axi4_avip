`ifndef AXI4_SLAVE_AGENT_CONFIG_INCLUDED_
`define AXI4_SLAVE_AGENT_CONFIG_INCLUDED_

//--------------------------------------------------------------------------------------------
// Class: axi4_slave_agent_config
// Used as the configuration class for axi4_slave agent and it's components
//--------------------------------------------------------------------------------------------
class axi4_slave_agent_config extends uvm_object;
  `uvm_object_utils(axi4_slave_agent_config)

  // Variable: is_active
  // Used for creating the agent in either passive or active mode
  uvm_active_passive_enum is_active=UVM_ACTIVE;  
  
  // Variable: has_coverage
  // Used for enabling the master agent coverage
  bit has_coverage;
  
  //-------------------------------------------------------
  // Externally defined Tasks and Functions
  //-------------------------------------------------------
  extern function new(string name = "axi4_slave_agent_config");
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

`endif

