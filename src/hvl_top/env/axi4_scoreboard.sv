`ifndef AXI4_SCOREBOARD_INCLUDED_
`define AXI4_SCOREBOARD_INCLUDED_

//--------------------------------------------------------------------------------------------
// Class: axi4_scoreboard
// Scoreboard the data getting from monitor port that goes into the implementation port
//--------------------------------------------------------------------------------------------
class axi4_scoreboard extends uvm_scoreboard;
  `uvm_component_utils(axi4_scoreboard)

  // Declaring handles for master tx and slave tx
  axi4_master_tx axi4_master_tx_h1;
  axi4_master_tx axi4_master_tx_h2;
  axi4_master_tx axi4_master_tx_h3;
  axi4_master_tx axi4_master_tx_h4;
  axi4_master_tx axi4_master_tx_h5;
  axi4_slave_tx  axi4_slave_tx_h1;
  axi4_slave_tx  axi4_slave_tx_h2;
  axi4_slave_tx  axi4_slave_tx_h3;
  axi4_slave_tx  axi4_slave_tx_h4;
  axi4_slave_tx  axi4_slave_tx_h5;

  //Variable : axi4_master_analysis_fifo
  //Used to store the axi4_master_data
  uvm_tlm_analysis_fifo#(axi4_master_tx) axi4_master_read_address_analysis_fifo;
  uvm_tlm_analysis_fifo#(axi4_master_tx) axi4_master_read_data_analysis_fifo;
  uvm_tlm_analysis_fifo#(axi4_master_tx) axi4_master_write_address_analysis_fifo;
  uvm_tlm_analysis_fifo#(axi4_master_tx) axi4_master_write_data_analysis_fifo;
  uvm_tlm_analysis_fifo#(axi4_master_tx) axi4_master_write_response_analysis_fifo;
  
  //Variable : axi4_slave_analysis_fifo
  //Used to store the axi4_slave_data
  uvm_tlm_analysis_fifo#(axi4_slave_tx) axi4_slave_read_address_analysis_fifo;
  uvm_tlm_analysis_fifo#(axi4_slave_tx) axi4_slave_read_data_analysis_fifo;
  uvm_tlm_analysis_fifo#(axi4_slave_tx) axi4_slave_write_address_analysis_fifo;
  uvm_tlm_analysis_fifo#(axi4_slave_tx) axi4_slave_write_data_analysis_fifo;
  uvm_tlm_analysis_fifo#(axi4_slave_tx) axi4_slave_write_response_analysis_fifo;

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
  axi4_master_read_address_analysis_fifo = new("axi4_master_read_address_analysis_fifo",this);
  axi4_master_read_data_analysis_fifo = new("axi4_master_read_data_analysis_fifo",this);
  axi4_master_write_address_analysis_fifo = new("axi4_master_write_address_analysis_fifo",this);
  axi4_master_write_data_analysis_fifo = new("axi4_master_write_data_analysis_fifo",this);
  axi4_master_write_response_analysis_fifo= new("axi4_master_write_response_analysis_fifo",this);
 
  axi4_slave_read_address_analysis_fifo = new("axi4_slave_read_address_analysis_fifo",this);
  axi4_slave_read_data_analysis_fifo = new("axi4_slave_read_data_analysis_fifo",this);
  axi4_slave_write_address_analysis_fifo = new("axi4_slave_write_address_analysis_fifo",this);
  axi4_slave_write_data_analysis_fifo = new("axi4_slave_write_data_analysis_fifo",this);
  axi4_slave_write_response_analysis_fifo= new("axi4_slave_write_response_analysis_fifo",this);
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

  super.run_phase(phase);

  forever begin
    `uvm_info(get_type_name(),$sformatf("calling analysis fifo in scoreboard"),UVM_HIGH);
    axi4_master_write_address_analysis_fifo.get(axi4_master_tx_h1);
    axi4_master_write_data_analysis_fifo.get(axi4_master_tx_h2);
    axi4_master_write_response_analysis_fifo.get(axi4_master_tx_h3);
    axi4_master_read_address_analysis_fifo.get(axi4_master_tx_h4);
    axi4_master_read_data_analysis_fifo.get(axi4_master_tx_h5);


    axi4_slave_write_address_analysis_fifo.get(axi4_slave_tx_h1);
    axi4_slave_write_data_analysis_fifo.get(axi4_slave_tx_h2);
    axi4_slave_write_response_analysis_fifo.get(axi4_slave_tx_h3);
    axi4_slave_read_address_analysis_fifo.get(axi4_slave_tx_h4);
    axi4_slave_read_data_analysis_fifo.get(axi4_slave_tx_h5);

    //-------------------------------------------------------
    // Printing data from all fifo's
    //-------------------------------------------------------

    // `uvm_info(get_type_name(),$sformatf("checking fifo used is %d",axi4_master_write_address_analysis_fifo.used()),UVM_HIGH)
    `uvm_info(get_type_name(),$sformatf("scoreboard's axi4_master_write_address \n%s",axi4_master_tx_h1.sprint()),UVM_HIGH)
    `uvm_info(get_type_name(),$sformatf("scoreboard's axi4_master_write_data \n%s",axi4_master_tx_h2.sprint()),UVM_HIGH)
    `uvm_info(get_type_name(),$sformatf("scoreboard's axi4_master_write_response \n%s",axi4_master_tx_h3.sprint()),UVM_HIGH)
    `uvm_info(get_type_name(),$sformatf("scoreboard's axi4_master_read_address \n%s",axi4_master_tx_h4.sprint()),UVM_HIGH)
    `uvm_info(get_type_name(),$sformatf("scoreboard's axi4_master_read_data \n%s",axi4_master_tx_h5.sprint()),UVM_HIGH)
    `uvm_info(get_type_name(),$sformatf("after printing all fifo's data in scoreboard"),UVM_HIGH);
    `uvm_info(get_type_name(),$sformatf("scoreboard's axi4_slave_write_address \n%s",axi4_slave_tx_h1.sprint()),UVM_HIGH)
    `uvm_info(get_type_name(),$sformatf("scoreboard's axi4_slave_write_data \n%s",axi4_slave_tx_h2.sprint()),UVM_HIGH)
    `uvm_info(get_type_name(),$sformatf("scoreboard's axi4_slave_write_response \n%s",axi4_slave_tx_h3.sprint()),UVM_HIGH)
    `uvm_info(get_type_name(),$sformatf("scoreboard's axi4_slave_read_address \n%s",axi4_slave_tx_h4.sprint()),UVM_HIGH)
    `uvm_info(get_type_name(),$sformatf("scoreboard's axi4_slave_read_data \n%s",axi4_slave_tx_h5.sprint()),UVM_HIGH)

    // Checking data for address in both master and slave
    foreach(axi4_master_tx_h1.awaddr[i])
    if(axi4_master_tx_h1.awaddr[i]!=axi4_slave_tx_h1.awaddr[i])
    begin
       `uvm_error("Scoreboard awaddr mismatch",$sformatf("awaddr[%0d] = %0h",i,axi4_master_tx_h1.awaddr[i]));;
    end
    else
    begin
      `uvm_info (get_type_name(), $sformatf ("scoreboard awaddr matched"),UVM_HIGH);
    end

  end
endtask : run_phase

`endif


