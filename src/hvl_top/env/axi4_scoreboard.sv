`ifndef AXI4_SCOREBOARD_INCLUDED_
`define AXI4_SCOREBOARD_INCLUDED_

//--------------------------------------------------------------------------------------------
// Class: axi4_scoreboard
// <Description_here>
//--------------------------------------------------------------------------------------------
class axi4_scoreboard extends uvm_scoreboard;
  `uvm_component_utils(axi4_scoreboard)

  //Variable : axi4_master_analysis_fifo
  //Used to store the axi4_master_data
  uvm_tlm_analysis_fifo#(axi4_master_tx) axi4_master_analysis_fifo;

  //Variable : axi4_slave_analysis_fifo
  //Used to store the axi4_slave_data
  uvm_tlm_analysis_fifo#(axi4_slave_tx) axi4_slave_analysis_fifo;
  

  //-------------------------------------------------------
  // Externally defined Tasks and Functions
  //-------------------------------------------------------
  extern function new(string name = "axi4_scoreboard", uvm_component parent = null);
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual function void connect_phase(uvm_phase phase);
  extern virtual function void end_of_elaboration_phase(uvm_phase phase);
  extern virtual function void start_of_simulation_phase(uvm_phase phase);
  extern virtual task run_phase(uvm_phase phase);

endclass : axi4_scoreboard

//--------------------------------------------------------------------------------------------
// Construct: new
//
// Parameters:
//  name - axi4_scoreboard
//  parent - parent under which this component is created
//--------------------------------------------------------------------------------------------
function axi4_scoreboard::new(string name = "axi4_scoreboard",
                                 uvm_component parent = null);
  super.new(name, parent);
  axi4_master_analysis_fifo = new("axi4_master_analysis_fifo",this);
  axi4_slave_analysis_fifo  = new("axi4_slave_analysis_fifo",this);
endfunction : new

//--------------------------------------------------------------------------------------------
// Function: build_phase
// <Description_here>
//
// Parameters:
//  phase - uvm phase
//--------------------------------------------------------------------------------------------
function void axi4_scoreboard::build_phase(uvm_phase phase);
  super.build_phase(phase);
endfunction : build_phase

//--------------------------------------------------------------------------------------------
// Function: connect_phase
// <Description_here>
//
// Parameters:
//  phase - uvm phase
//--------------------------------------------------------------------------------------------
function void axi4_scoreboard::connect_phase(uvm_phase phase);
  super.connect_phase(phase);
endfunction : connect_phase

//--------------------------------------------------------------------------------------------
// Function: end_of_elaboration_phase
// <Description_here>
//
// Parameters:
//  phase - uvm phase
//--------------------------------------------------------------------------------------------
function void axi4_scoreboard::end_of_elaboration_phase(uvm_phase phase);
  super.end_of_elaboration_phase(phase);
endfunction  : end_of_elaboration_phase

//--------------------------------------------------------------------------------------------
// Function: start_of_simulation_phase
// <Description_here>
//
// Parameters:
//  phase - uvm phase
//--------------------------------------------------------------------------------------------
function void axi4_scoreboard::start_of_simulation_phase(uvm_phase phase);
  super.start_of_simulation_phase(phase);
endfunction : start_of_simulation_phase

//--------------------------------------------------------------------------------------------
// Task: run_phase
// <Description_here>
//
// Parameters:
//  phase - uvm phase
//--------------------------------------------------------------------------------------------
task axi4_scoreboard::run_phase(uvm_phase phase);

  phase.raise_objection(this, "axi4_scoreboard");

  super.run_phase(phase);

  // Work here
  // ...

  phase.drop_objection(this);

endtask : run_phase

`endif

