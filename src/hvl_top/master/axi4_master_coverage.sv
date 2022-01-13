`ifndef AXI4_MASTER_COVERAGE_INCLUDED_
`define AXI4_MASTER_COVERAGE_INCLUDED_

//--------------------------------------------------------------------------------------------
// Class: master_coverage
// master_coverage determines the how much code is covered for better functionality of the TB.
//--------------------------------------------------------------------------------------------
class axi4_master_coverage extends uvm_subscriber #(axi4_master_tx);
  `uvm_component_utils(axi4_master_coverage)

  // Variable: axi4_master_agent_cfg_h
  // Declaring handle for master agent configuration class 
  axi4_master_agent_config axi4_master_agent_cfg_h;
  
  // Variable: axi4_master_analysis_export
  //declaring analysis port for coverage
  uvm_analysis_port#(axi4_master_tx) axi4_master_read_address_analysis_port;
  uvm_analysis_port#(axi4_master_tx) axi4_master_read_data_analysis_port;
  uvm_analysis_port#(axi4_master_tx) axi4_master_write_address_analysis_port;
  uvm_analysis_port#(axi4_master_tx) axi4_master_write_data_analysis_port;
  uvm_analysis_port#(axi4_master_tx) axi4_master_write_response_analysis_port;

  //-------------------------------------------------------
  // Externally defined Tasks and Functions
  //-------------------------------------------------------
  extern function new(string name = "axi4_master_coverage", uvm_component parent = null);
  extern virtual function void write(axi4_master_tx t);
  extern virtual function void report_phase(uvm_phase phase);

endclass : axi4_master_coverage

//--------------------------------------------------------------------------------------------
// Construct: new
//
// Parameters:
//  name - axi4_master_coverage
//  parent - parent under which this component is created
//--------------------------------------------------------------------------------------------
function axi4_master_coverage::new(string name = "axi4_master_coverage",
                                 uvm_component parent = null);
  super.new(name, parent);
  axi4_master_read_address_analysis_port = new("axi4_master_read_address_analysis_port",this);
  axi4_master_read_data_analysis_port = new("axi4_master_read_data_analysis_port",this);
  axi4_master_write_address_analysis_port = new("axi4_master_write_address_analysis_port",this);
  axi4_master_write_data_analysis_port = new("axi4_master_write_data_analysis_port",this);
  axi4_master_write_response_analysis_port = new("axi4_master_write_response_analysis_port",this);

endfunction : new

//--------------------------------------------------------------------------------------------
// Function: write
// sampiling is done
//--------------------------------------------------------------------------------------------
function void axi4_master_coverage::write(axi4_master_tx t);

endfunction: write

//--------------------------------------------------------------------------------------------
// Function: report_phase
// Used for reporting the coverage instance percentage values
//--------------------------------------------------------------------------------------------
function void axi4_master_coverage::report_phase(uvm_phase phase);

endfunction: report_phase

`endif

