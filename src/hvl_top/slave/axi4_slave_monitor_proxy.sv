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

  // Variable: axi4_slave_agent_cfg_h;
  // Handle for axi4 slave agent configuration
  axi4_slave_agent_config axi4_slave_agent_cfg_h;

  //Declaring Monitor Analysis Import
  uvm_analysis_port #(axi4_slave_tx) axi4_slave_analysis_port;

  //Declaring Virtual Monitor BFM Handle
  virtual axi4_slave_monitor_bfm axi4_slave_mon_bfm_h;

  //-------------------------------------------------------
  // Externally defined Tasks and Functions
  //-------------------------------------------------------
  extern function new(string name = "axi4_slave_monitor_proxy", uvm_component parent = null);
  extern virtual function void build_phase(uvm_phase phase);
  extern function void end_of_elaboration_phase(uvm_phase phase);
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
  axi4_slave_analysis_port = new("axi4_slave_analysis_port",this);
  
endfunction : new

//--------------------------------------------------------------------------------------------
// Function: build_phase
//
// Parameters:
//  phase - uvm phase
//--------------------------------------------------------------------------------------------
function void axi4_slave_monitor_proxy::build_phase(uvm_phase phase);
  super.build_phase(phase);
   if(!uvm_config_db#(virtual axi4_slave_monitor_bfm)::get(this,"","axi4_slave_monitor_bfm",axi4_slave_mon_bfm_h)) begin
     `uvm_fatal("FATAL_SMP_MON_BFM",$sformatf("Couldn't get S_MON_BFM in axi4_slave_monitor_proxy"));  
  end 
endfunction : build_phase

//-------------------------------------------------------
// Function: end_of_elaboration_phase
//Description: connects monitor_proxy and monitor_bfm
//
// Parameters:
//  phase - stores the current phase
//-------------------------------------------------------
function void axi4_slave_monitor_proxy::end_of_elaboration_phase(uvm_phase phase);
  super.end_of_elaboration_phase(phase);
  axi4_slave_mon_bfm_h.axi4_slave_mon_proxy_h = this;
endfunction : end_of_elaboration_phase


//--------------------------------------------------------------------------------------------
// Task: run_phase
//--------------------------------------------------------------------------------------------
task axi4_slave_monitor_proxy::run_phase(uvm_phase phase);

endtask : run_phase 

`endif
