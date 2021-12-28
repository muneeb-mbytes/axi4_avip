`ifndef AXI4_ENV_INCLUDED_
`define AXI4_ENV_INCLUDED_

//--------------------------------------------------------------------------------------------
// Class: axi4 env
// Description:
// Environment contains slave_agent_top,master_agent_top and virtual_sequencer
//--------------------------------------------------------------------------------------------
class axi4_env extends uvm_env;
  `uvm_component_utils(axi4_env)
  
  axi4_env_config axi4_env_cfg_h;
  
  axi4_master_agent axi4_master_agent_h;
  
  axi4_slave_agent axi4_slave_agent_h;

  virtual_sequencer virtual_seqr_h;

  axi4_scoreboard axi4_scoreboard_h;
 
  //-------------------------------------------------------
  // Externally defined Tasks and Functions
  //-------------------------------------------------------
  extern function new(string name = "axi4_env", uvm_component parent = null);
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual function void connect_phase(uvm_phase phase);

endclass : axi4_env

//--------------------------------------------------------------------------------------------
// Construct: new
//
// Parameters:
// name - axi4_env
// parent - parent under which this component is created
//--------------------------------------------------------------------------------------------
function axi4_env::new(string name = "axi4_env",uvm_component parent = null);
  super.new(name, parent);
endfunction : new

//--------------------------------------------------------------------------------------------
// Function: build_phase
// Description:
// Create required components
//
// Parameters:
// phase - uvm phase
//--------------------------------------------------------------------------------------------
function void axi4_env::build_phase(uvm_phase phase);
  super.build_phase(phase);
  
  if(!uvm_config_db #(axi4_env_config)::get(this,"","axi4_env_config",axi4_env_cfg_h)) begin
   `uvm_fatal("FATAL_SA_AGENT_CONFIG", $sformatf("Couldn't get the slave_agent_config from config_db"))
  end
  axi4_master_agent_h=axi4_master_agent::type_id::create("axi4_master_agent_h",this);
  axi4_slave_agent_h=axi4_slave_agent::type_id::create("axi4_slave_agent_h",this);
  
  if(axi4_env_cfg_h.has_virtual_seqr) begin
    virtual_seqr_h = virtual_sequencer::type_id::create("virtual_seqr_h",this);
  end

  if(axi4_env_cfg_h.has_scoreboard) begin
  axi4_scoreboard_h=axi4_scoreboard::type_id::create("axi4_scoreboard_h",this);
  end
endfunction : build_phase

//--------------------------------------------------------------------------------------------
// Function: connect_phase
// Description:
// To connect driver and sequencer
//
// Parameters:
// phase - uvm phase
//--------------------------------------------------------------------------------------------
function void axi4_env::connect_phase(uvm_phase phase);
  super.connect_phase(phase);

  if(axi4_env_cfg_h.has_virtual_seqr) begin
    virtual_seqr_h.axi4_master_seqr_h = axi4_master_agent_h.axi4_master_seqr_h;
      virtual_seqr_h.axi4_slave_seqr_h = axi4_slave_agent_h.axi4_slave_seqr_h;
    end
endfunction : connect_phase

`endif

