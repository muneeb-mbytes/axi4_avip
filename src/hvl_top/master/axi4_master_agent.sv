`ifndef AXI4_MASTER_AGENT_INCLUDED_
`define AXI4_MASTER_AGENT_INCLUDED_

//--------------------------------------------------------------------------------------------
// Class: axi4_master_agent
// <Description_here>
//--------------------------------------------------------------------------------------------
class axi4_master_agent extends uvm_agent;
  `uvm_component_utils(axi4_master_agent)

  // Variable: axi4_master_agent_cfg_h
  // Declaring handle for master agent configuration class 
  axi4_master_agent_config axi4_master_agent_cfg_h;

  // Varible: axi4_master_seqr_h 
  // Handle for master seuencer
  axi4_master_sequencer axi4_master_seqr_h;
  
  // Variable: axi4_master_drv_proxy_h
  // Creating a Handle for axi4_master driver proxy 
  axi4_master_driver_proxy axi4_master_drv_proxy_h;

  // Variable: axi4_master_mon_proxy_h
  // Declaring a handle for axi4_master monitor proxy 
  axi4_master_monitor_proxy axi4_master_mon_proxy_h;
  
  // MSHA: // Variable: axi4_master_coverage
  // MSHA: // Decalring a handle for axi4_master_coverage
   axi4_master_coverage axi4_master_cov_h;
  //-------------------------------------------------------
  // Externally defined Tasks and Functions
  //-------------------------------------------------------
  extern function new(string name = "axi4_master_agent", uvm_component parent = null);
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual function void connect_phase(uvm_phase phase);
  extern virtual function void end_of_elaboration_phase(uvm_phase phase);
  extern virtual function void start_of_simulation_phase(uvm_phase phase);
  extern virtual task run_phase(uvm_phase phase);

endclass : axi4_master_agent

//--------------------------------------------------------------------------------------------
// Construct: new
//
// Parameters:
//  name - axi4_master_agent
//  parent - parent under which this component is created
//--------------------------------------------------------------------------------------------
function axi4_master_agent::new(string name = "axi4_master_agent",
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
function void axi4_master_agent::build_phase(uvm_phase phase);
  super.build_phase(phase);
  
  if(!uvm_config_db #(axi4_master_agent_config)::get(this,"","axi4_master_agent_config",axi4_master_agent_cfg_h)) begin
    `uvm_fatal("FATAL_MA_CANNOT_GET_MASTER_AGENT_CONFIG","cannot get axi4_master_agent_cfg_h from uvm_config_db");
  end
  if(axi4_master_agent_cfg_h.is_active == UVM_ACTIVE) begin
    axi4_master_drv_proxy_h=axi4_master_driver_proxy::type_id::create("axi4_master_drv_proxy_h",this);
    axi4_master_seqr_h=axi4_master_sequencer::type_id::create("axi4_master_seqr_h",this);
  end

  axi4_master_mon_proxy_h=axi4_master_monitor_proxy::type_id::create("axi4_master_mon_proxy_h",this);

endfunction : build_phase

//--------------------------------------------------------------------------------------------
// Function: connect_phase
// <Description_here>
//
// Parameters:
//  phase - uvm phase
//--------------------------------------------------------------------------------------------
function void axi4_master_agent::connect_phase(uvm_phase phase);
  super.connect_phase(phase);
  if(axi4_master_agent_cfg_h.is_active == UVM_ACTIVE) begin
    axi4_master_drv_proxy_h.axi4_master_agent_cfg_h = axi4_master_agent_cfg_h;
    axi4_master_seqr_h.axi4_master_agent_cfg_h = axi4_master_agent_cfg_h;

    //Connecting the ports
    axi4_master_drv_proxy_h.seq_item_port.connect(axi4_master_seqr_h.seq_item_export);
  end
  
  axi4_master_mon_proxy_h.axi4_master_agent_cfg_h = axi4_master_agent_cfg_h;

endfunction : connect_phase

//--------------------------------------------------------------------------------------------
// Function: end_of_elaboration_phase
// <Description_here>
//
// Parameters:
//  phase - uvm phase
//--------------------------------------------------------------------------------------------
function void axi4_master_agent::end_of_elaboration_phase(uvm_phase phase);
  super.end_of_elaboration_phase(phase);
endfunction  : end_of_elaboration_phase

//--------------------------------------------------------------------------------------------
// Function: start_of_simulation_phase
// <Description_here>
//
// Parameters:
//  phase - uvm phase
//--------------------------------------------------------------------------------------------
function void axi4_master_agent::start_of_simulation_phase(uvm_phase phase);
  super.start_of_simulation_phase(phase);
endfunction : start_of_simulation_phase

//--------------------------------------------------------------------------------------------
// Task: run_phase
// <Description_here>
//
// Parameters:
//  phase - uvm phase
//--------------------------------------------------------------------------------------------
task axi4_master_agent::run_phase(uvm_phase phase);

  phase.raise_objection(this, "axi4_master_agent");

  super.run_phase(phase);

  // Work here
  // ...

  phase.drop_objection(this);

endtask : run_phase

`endif

