`ifndef AXI4_SLAVE_MONITOR_PROXY_INCLUDED_
`define AXI4_SLAVE_MONITOR_PROXY_INCLUDED_

//--------------------------------------------------------------------------------------------
// Class: axi4_slave_monitor_proxy
// This is the HVL axi4_slave monitor proxy
// It gets the sampled data from the HDL axi4_slave monitor and 
// converts them into transaction items
//--------------------------------------------------------------------------------------------
class axi4_slave_monitor_proxy extends uvm_monitor;
  `uvm_component_utils(axi4_slave_monitor_proxy)

  axi4_slave_agent_config axi4_slave_agent_cfg_h;

  //-------------------------------------------------------
  // Externally defined Tasks and Functions
  //-------------------------------------------------------
  extern function new(string name = "axi4_slave_monitor_proxy", uvm_component parent = null);
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual task run_phase(uvm_phase phase);

endclass : axi4_slave_monitor_proxy

//--------------------------------------------------------------------------------------------
// Construct: new
//
// Parameters:
//  name - axi4_slave_monitor_proxy
//  parent - parent under which this component is created
//--------------------------------------------------------------------------------------------
function axi4_slave_monitor_proxy::new(string name = "axi4_slave_monitor_proxy",
                                 uvm_component parent = null);
  super.new(name, parent);
endfunction : new

//--------------------------------------------------------------------------------------------
// Function: build_phase
//
// Parameters:
//  phase - uvm phase
//--------------------------------------------------------------------------------------------
function void axi4_slave_monitor_proxy::build_phase(uvm_phase phase);
  super.build_phase(phase);
endfunction : build_phase

//--------------------------------------------------------------------------------------------
// Task: run_phase
//--------------------------------------------------------------------------------------------
task axi4_slave_monitor_proxy::run_phase(uvm_phase phase);

endtask : run_phase 

`endif
