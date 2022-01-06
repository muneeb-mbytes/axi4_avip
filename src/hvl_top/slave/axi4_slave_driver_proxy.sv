`ifndef AXI4_SLAVE_DRIVER_PROXY_INCLUDED_
`define AXI4_SLAVE_DRIVER_PROXY_INCLUDED_

//--------------------------------------------------------------------------------------------
// Class: axi4_slave_driver_proxy
// This is the proxy driver on the HVL side
// It receives the transactions and converts them to task calls for the HDL driver
//--------------------------------------------------------------------------------------------
class axi4_slave_driver_proxy extends uvm_driver#(axi4_slave_tx);
  `uvm_component_utils(axi4_slave_driver_proxy)

  // Port: seq_item_port
  //
  // Derived driver classes should use this port to request items from the
  // sequencer. They may also use it to send responses back.
  
  uvm_seq_item_pull_port #(REQ, RSP) axi_write_seq_item_port;
  uvm_seq_item_pull_port #(REQ, RSP) axi_read_seq_item_port;

  // Port: rsp_port
  //
  // This port provides an alternate way of sending responses back to the
  // originating sequencer. Which port to use depends on which export the
  // sequencer provides for connection.
  
  uvm_analysis_port #(RSP) axi_write_rsp_port;
  uvm_analysis_port #(RSP) axi_read_rsp_port;
  
  REQ req;
  RSP rsp;

  // Variable: axi4_slave_agent_cfg_h
  // Declaring handle for axi4_slave agent config class 
  axi4_slave_agent_config axi4_slave_agent_cfg_h;

  //Variable : axi4_slave_drv_bfm_h
  //Declaring handle for axi4 driver bfm
  virtual axi4_slave_driver_bfm axi4_slave_drv_bfm_h;

  //-------------------------------------------------------
  // Externally defined Tasks and Functions
  //-------------------------------------------------------
  extern function new(string name = "axi4_slave_driver_proxy", uvm_component parent = null);
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual function void end_of_elaboration_phase(uvm_phase phase);
  extern virtual task run_phase(uvm_phase phase);
  extern virtual task axi_write_task(uvm_phase phase);
  extern virtual task axi_read_task(uvm_phase phase);

endclass : axi4_slave_driver_proxy

//--------------------------------------------------------------------------------------------
// Construct: new
// Parameters:
//  name - axi4_slave_driver_proxy
//  parent - parent under which this component is created
//--------------------------------------------------------------------------------------------
function axi4_slave_driver_proxy::new(string name = "axi4_slave_driver_proxy",
                                 uvm_component parent = null);
  super.new(name, parent);
  axi_write_seq_item_port    = new("axi_write_seq_item_port", this);
  axi_read_seq_item_port     = new("axi_read_seq_item_port", this);
  axi_write_rsp_port         = new("axi_write_rsp_port", this);
  axi_read_rsp_port          = new("axi_read_rsp_port", this);
endfunction : new

//--------------------------------------------------------------------------------------------
// Function: build_phase
//
// Parameters:
//  phase - uvm phase
//--------------------------------------------------------------------------------------------
function void axi4_slave_driver_proxy::build_phase(uvm_phase phase);
  super.build_phase(phase);
  if(!uvm_config_db #(virtual axi4_slave_driver_bfm)::get(this,"","axi4_slave_driver_bfm",axi4_slave_drv_bfm_h)) begin
    `uvm_fatal("FATAL_MDP_CANNOT_GET_tx_DRIVER_BFM","cannot get() axi4_slave_drv_bfm_h");
  end
endfunction : build_phase

//--------------------------------------------------------------------------------------------
// Function: end_of_elaboration_phase
//
// Parameters:
// phase - uvm phase
//--------------------------------------------------------------------------------------------
function void axi4_slave_driver_proxy::end_of_elaboration_phase(uvm_phase phase);
  super.end_of_elaboration_phase(phase);
  axi4_slave_drv_bfm_h.axi4_slave_drv_proxy_h= this;
endfunction  : end_of_elaboration_phase


//--------------------------------------------------------------------------------------------
// Task: run_phase
//--------------------------------------------------------------------------------------------
task axi4_slave_driver_proxy::run_phase(uvm_phase phase);

  `uvm_info(get_type_name(),"SLAVE_DRIVER_PROXY",UVM_MEDIUM)
  
  axi4_slave_drv_bfm_h.wait_for_system_reset();

  forever begin

    axi4_w_transfer_char_s struct_write_packet_char;
    axi4_r_transfer_char_s struct_read_packet_char;
    axi4_transfer_cfg_s    struct_cfg;

    //seq_item_port.get_next_item(req);

   // axi4_slave_seq_item_converter::from_w_class(req,struct_write_packet_char);
   // axi4_slave_seq_item_converter::from_r_class(req,struct_read_packet_char);
   // axi4_slave_cfg_converter::from_class(axi4_slave_agent_cfg_h,struct_cfg);

    fork
   //   axi4_slave_drv_bfm_h.axi_write_address_phase(struct_write_packet_char);
   //   axi4_slave_drv_bfm_h.axi_write_data_phase(struct_write_packet_char,struct_cfg);
    join_none

    //seq_item_port.finish_item();

  end

endtask : run_phase 

task axi4_slave_driver_proxy::axi_write_task(uvm_phase phase);
  axi_write_seq_item_port.get_next_item(req);

  //axi_write_seq_item_port.finish_item();
endtask

task axi4_slave_driver_proxy::axi_read_task(uvm_phase phase);
  axi_read_seq_item_port.get_next_item(req);

  //axi_write_seq_item_port.finish_item();
endtask

`endif
