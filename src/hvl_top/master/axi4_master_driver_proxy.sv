`ifndef AXI4_MASTER_DRIVER_PROXY_INCLUDED_
`define AXI4_MASTER_DRIVER_PROXY_INCLUDED_

//--------------------------------------------------------------------------------------------
// Class: axi4_master_driver_proxy
// <Description_here>
//--------------------------------------------------------------------------------------------
class axi4_master_driver_proxy extends uvm_driver#(axi4_master_tx);
  `uvm_component_utils(axi4_master_driver_proxy)

  // Variable: axi4_master_agent_cfg_h
  // Declaring handle for axi4_master agent config class 
  axi4_master_agent_config axi4_master_agent_cfg_h;

  //Variable : axi4_master_drv_bfm_h
  //Declaring handle for axi4 driver bfm
  virtual axi4_master_driver_bfm axi4_master_drv_bfm_h;
  
  //-------------------------------------------------------
  // Externally defined Tasks and Functions
  //-------------------------------------------------------
  extern function new(string name = "axi4_master_driver_proxy", uvm_component parent = null);
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual function void connect_phase(uvm_phase phase);
  extern virtual function void end_of_elaboration_phase(uvm_phase phase);
  extern virtual function void start_of_simulation_phase(uvm_phase phase);
  extern virtual task run_phase(uvm_phase phase);

endclass : axi4_master_driver_proxy

//--------------------------------------------------------------------------------------------
// Construct: new
//
// Parameters:
//  name - axi4_master_driver_proxy
//  parent - parent under which this component is created
//--------------------------------------------------------------------------------------------
function axi4_master_driver_proxy::new(string name = "axi4_master_driver_proxy",
                                 uvm_component parent = null);
  super.new(name, parent);
endfunction : new

//--------------------------------------------------------------------------------------------
// Function: build_phase
// <Description_here>
//
// Parameters:
//  phase - uvm phase
//--------------------------------------------------------------------------------------------
function void axi4_master_driver_proxy::build_phase(uvm_phase phase);
  super.build_phase(phase);
  if(!uvm_config_db #(virtual axi4_master_driver_bfm)::get(this,"","axi4_master_driver_bfm",axi4_master_drv_bfm_h)) begin
    `uvm_fatal("FATAL_MDP_CANNOT_GET_AXI4_MASTER_DRIVER_BFM","cannot get() axi4_master_drv_bfm_h");
  end
endfunction : build_phase

//--------------------------------------------------------------------------------------------
// Function: connect_phase
// <Description_here>
//
// Parameters:
//  phase - uvm phase
//--------------------------------------------------------------------------------------------
function void axi4_master_driver_proxy::connect_phase(uvm_phase phase);
  super.connect_phase(phase);
endfunction : connect_phase

//--------------------------------------------------------------------------------------------
// Function: end_of_elaboration_phase
// <Description_here>
//
// Parameters:
//  phase - uvm phase
//--------------------------------------------------------------------------------------------
function void axi4_master_driver_proxy::end_of_elaboration_phase(uvm_phase phase);
  super.end_of_elaboration_phase(phase);
  axi4_master_drv_bfm_h.axi4_master_drv_proxy_h = this;
endfunction  : end_of_elaboration_phase

//--------------------------------------------------------------------------------------------
// Function: start_of_simulation_phase
// <Description_here>
//
// Parameters:
//  phase - uvm phase
//--------------------------------------------------------------------------------------------
function void axi4_master_driver_proxy::start_of_simulation_phase(uvm_phase phase);
  super.start_of_simulation_phase(phase);
endfunction : start_of_simulation_phase

//--------------------------------------------------------------------------------------------
// Task: run_phase
// <Description_here>
//
// Parameters:
//  phase - uvm phase
//--------------------------------------------------------------------------------------------
task axi4_master_driver_proxy::run_phase(uvm_phase phase);

  phase.raise_objection(this, "axi4_master_driver_proxy");

  super.run_phase(phase);

  // Work here
  // ...

  phase.drop_objection(this);

endtask : run_phase

`endif

