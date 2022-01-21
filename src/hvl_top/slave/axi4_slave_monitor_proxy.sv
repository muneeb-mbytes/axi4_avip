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

  // Declaring Virtual Monitor BFM Handle
  virtual axi4_slave_monitor_bfm axi4_slave_mon_bfm_h;

  axi4_slave_tx req_rd;
  axi4_slave_tx req_wr;

  // Variable: axi4_slave_analysis_port
  // Declaring analysis port for the monitor port
  uvm_analysis_port#(axi4_slave_tx) axi4_slave_write_address_analysis_port;
  uvm_analysis_port#(axi4_slave_tx) axi4_slave_write_data_analysis_port;
  uvm_analysis_port#(axi4_slave_tx) axi4_slave_write_response_analysis_port;
  uvm_analysis_port#(axi4_slave_tx) axi4_slave_read_address_analysis_port;
  uvm_analysis_port#(axi4_slave_tx) axi4_slave_read_data_analysis_port;
  
  //-------------------------------------------------------
  // Externally defined Tasks and Functions
  //-------------------------------------------------------
  extern function new(string name = "axi4_slave_monitor_proxy", uvm_component parent = null);
  extern virtual function void build_phase(uvm_phase phase);
  extern function void end_of_elaboration_phase(uvm_phase phase);
  extern virtual task run_phase(uvm_phase phase);
  extern virtual task axi4_slave_write_address();
  extern virtual task axi4_slave_write_data();
  extern virtual task axi4_slave_write_response();
  extern virtual task axi4_slave_read_address();
  extern virtual task axi4_slave_read_data();


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
  axi4_slave_read_address_analysis_port = new("axi4_slave_read_address_analysis_port",this);
  axi4_slave_read_data_analysis_port = new("axi4_slave_read_data_analysis_port",this);
  axi4_slave_write_address_analysis_port = new("axi4_slave_write_address_analysis_port",this);
  axi4_slave_write_data_analysis_port = new("axi4_slave_write_data_analysis_port",this);
  axi4_slave_write_response_analysis_port = new("axi4_slave_write_response_analysis_port",this);
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

  fork 
    axi4_slave_write_address();
    axi4_slave_write_data();
    axi4_slave_write_response();
    axi4_slave_read_address();
    axi4_slave_read_data();
  join

endtask : run_phase 
//-------------------------------------------------------
// Task : axi4_slave_monitor_proxy
// Description: converting,sampling and again converting 
//-------------------------------------------------------
task axi4_slave_monitor_proxy::axi4_slave_write_address();
  forever begin
    axi4_write_transfer_char_s struct_write_packet;
    axi4_transfer_cfg_s        struct_cfg;
    axi4_slave_tx              req_wr_clone_packet;


    axi4_slave_mon_bfm_h.wait_for_aresetn();
    axi4_slave_cfg_converter::from_class(axi4_slave_agent_cfg_h, struct_cfg);
    axi4_slave_mon_bfm_h.axi4_slave_write_address_sampling(struct_write_packet,struct_cfg);
    `uvm_info(get_type_name(),$sformatf(" DEBUG_CHE = %p",struct_write_packet),UVM_HIGH)
    axi4_slave_seq_item_converter::to_write_class(struct_write_packet,req_wr);
    
    $cast(req_wr_clone_packet,req_wr.clone());    
    `uvm_info(get_type_name(),$sformatf("Packet received from axi4_slave_write_address_sampling is %s",req_wr.sprint()),UVM_HIGH)
    axi4_slave_write_address_analysis_port.write(req_wr_clone_packet);

  end
endtask

task axi4_slave_monitor_proxy::axi4_slave_write_data();

endtask

task axi4_slave_monitor_proxy::axi4_slave_write_response();

endtask

task axi4_slave_monitor_proxy::axi4_slave_read_address();

endtask

task axi4_slave_monitor_proxy::axi4_slave_read_data();
forever begin
    axi4_read_transfer_char_s struct_read_packet;
    axi4_transfer_cfg_s       struct_cfg;
    axi4_slave_tx             req_rd_clone_packet; 

    `uvm_info(get_type_name(), $sformatf("DEBUG :: Inside axi4_read_data"), UVM_NONE);
    
    axi4_slave_cfg_converter::from_class(axi4_slave_agent_cfg_h, struct_cfg);
    axi4_slave_mon_bfm_h.axi4_read_data_sampling(struct_read_packet,struct_cfg);
    `uvm_info(get_type_name(), $sformatf("DEBUG :: From Slave MON BFM :: Read data: %p ",struct_read_packet), UVM_NONE);
    axi4_slave_seq_item_converter::to_read_class(struct_read_packet,req_rd);

    $cast(req_rd_clone_packet,req_rd.clone());
    `uvm_info(get_type_name(),$sformatf("Packet received from axi4_read_data_sampling is %p",req_rd.sprint()),UVM_HIGH)
    `uvm_info(get_type_name(),$sformatf("Packet received from axi4_read_data_sampling clone packet is %p",req_rd_clone_packet.sprint()),UVM_HIGH)

    axi4_slave_read_data_analysis_port.write(req_rd);
  end
endtask


`endif
