`ifndef AXI4_MASTER_MONITOR_PROXY_INCLUDED_
`define AXI4_MASTER_MONITOR_PROXY_INCLUDED_

//--------------------------------------------------------------------------------------------
//  Class: axi4_master_monitor_proxy
//  
//  Monitor is written by extending uvm_monitor,uvm_monitor is inherited from uvm_component, 
//  A monitor is a passive entity that samples the DUT signals through virtual interface and 
//  converts the signal level activity to transaction level,monitor samples DUT signals but does not drive them.
//  Monitor should have analysis port (TLM port) and virtual interface handle that points to DUT signal
//--------------------------------------------------------------------------------------------
class axi4_master_monitor_proxy extends uvm_component;
  `uvm_component_utils(axi4_master_monitor_proxy)

  // Variable: axi4_master_agent_cfg_h
  // Declaring handle for axi4_master agent config class 
  axi4_master_agent_config axi4_master_agent_cfg_h;

  axi4_master_tx req_rd;
  axi4_master_tx req_wr;

  //Variable : apb_master_mon_bfm_h
  //Declaring handle for apb monitor bfm
  virtual axi4_master_monitor_bfm axi4_master_mon_bfm_h;
  
  // Variable: apb_master_analysis_port
  //declaring analysis port for the monitor port
  uvm_analysis_port#(axi4_master_tx) axi4_master_read_address_analysis_port;
  uvm_analysis_port#(axi4_master_tx) axi4_master_read_data_analysis_port;
  uvm_analysis_port#(axi4_master_tx) axi4_master_write_address_analysis_port;
  uvm_analysis_port#(axi4_master_tx) axi4_master_write_data_analysis_port;
  uvm_analysis_port#(axi4_master_tx) axi4_master_write_response_analysis_port;


  //-------------------------------------------------------
  // Externally defined Tasks and Functions
  //-------------------------------------------------------
  extern function new(string name = "axi4_master_monitor_proxy", uvm_component parent = null);
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual function void connect_phase(uvm_phase phase);
  extern virtual function void end_of_elaboration_phase(uvm_phase phase);
  extern virtual function void start_of_simulation_phase(uvm_phase phase);
  extern virtual task run_phase(uvm_phase phase);
  extern virtual task axi4_write_address();
  extern virtual task axi4_write_data();
  extern virtual task axi4_write_response();
  extern virtual task axi4_read_address();
  extern virtual task axi4_read_data();


endclass : axi4_master_monitor_proxy

//--------------------------------------------------------------------------------------------
// Construct: new
//
// Parameters:
//  name - axi4_master_monitor_proxy
//  parent - parent under which this component is created
//--------------------------------------------------------------------------------------------
function axi4_master_monitor_proxy::new(string name = "axi4_master_monitor_proxy",
                                 uvm_component parent = null);
  super.new(name, parent);
  axi4_master_read_address_analysis_port = new("axi4_master_read_address_analysis_port",this);
  axi4_master_read_data_analysis_port = new("axi4_master_read_data_analysis_port",this);
  axi4_master_write_address_analysis_port = new("axi4_master_write_address_analysis_port",this);
  axi4_master_write_data_analysis_port = new("axi4_master_write_data_analysis_port",this);
  axi4_master_write_response_analysis_port = new("axi4_master_write_response_analysis_port",this);
endfunction : new

//--------------------------------------------------------------------------------------------
// Function: build_phase
//
// Parameters:
//  phase - uvm phase
//--------------------------------------------------------------------------------------------
function void axi4_master_monitor_proxy::build_phase(uvm_phase phase);
  super.build_phase(phase);
  if(!uvm_config_db #(virtual axi4_master_monitor_bfm)::get(this,"","axi4_master_monitor_bfm",axi4_master_mon_bfm_h)) begin
    `uvm_fatal("FATAL_MDP_CANNOT_GET_AXI4_MASTER_MONITOR_BFM","cannot get() axi4_master_mon_bfm_h");
  end 
endfunction : build_phase

//--------------------------------------------------------------------------------------------
// Function: connect_phase
// <Description_here>
//
// Parameters:
//  phase - uvm phase
//--------------------------------------------------------------------------------------------
function void axi4_master_monitor_proxy::connect_phase(uvm_phase phase);
  super.connect_phase(phase);
endfunction : connect_phase

//--------------------------------------------------------------------------------------------
// Function: end_of_elaboration_phase
// <Description_here>
//
// Parameters:
//  phase - uvm phase
//--------------------------------------------------------------------------------------------
function void axi4_master_monitor_proxy::end_of_elaboration_phase(uvm_phase phase);
  super.end_of_elaboration_phase(phase);
  axi4_master_mon_bfm_h.axi4_master_mon_proxy_h = this;
endfunction  : end_of_elaboration_phase

//--------------------------------------------------------------------------------------------
// Function: start_of_simulation_phase
// <Description_here>
//
// Parameters:
//  phase - uvm phase
//--------------------------------------------------------------------------------------------
function void axi4_master_monitor_proxy::start_of_simulation_phase(uvm_phase phase);
  super.start_of_simulation_phase(phase);
endfunction : start_of_simulation_phase

//--------------------------------------------------------------------------------------------
// Task: run_phase
// <Description_here>
//
// Parameters:
//  phase - uvm phase
//--------------------------------------------------------------------------------------------
task axi4_master_monitor_proxy::run_phase(uvm_phase phase);

  axi4_master_mon_bfm_h.wait_for_aresetn();

  fork 
    axi4_write_address();
    axi4_write_data();
    axi4_write_response();
    axi4_read_address();
    axi4_read_data();
  join

endtask : run_phase

task axi4_master_monitor_proxy::axi4_write_address();
  forever begin
    axi4_write_transfer_char_s struct_write_packet;
    axi4_transfer_cfg_s        struct_cfg;
    axi4_master_tx             req_wr_clone_packet;

    `uvm_info(get_type_name(), $sformatf("DEBUG_MSHA :: Inside axi4_write_address"), UVM_NONE); 
    axi4_master_cfg_converter::from_class(axi4_master_agent_cfg_h, struct_cfg);
    axi4_master_mon_bfm_h.axi4_write_address_sampling(struct_write_packet,struct_cfg);
    axi4_master_seq_item_converter::to_write_class(struct_write_packet,req_wr);

    $cast(req_wr_clone_packet,req_wr.clone());
    `uvm_info(get_type_name(),$sformatf("Packet received from axi4_write_address_sampling is %p",req_wr.sprint()),UVM_HIGH)
    `uvm_info(get_type_name(),$sformatf("Packet received from axi4_write_address_sampling clone packet is %p",req_wr_clone_packet.sprint()),UVM_HIGH)

    axi4_master_read_address_analysis_port.write(req_wr);
    // print value
    // sending the packet via analysis port
  end
endtask

task axi4_master_monitor_proxy::axi4_write_data();
  forever begin
    axi4_write_transfer_char_s struct_write_packet;
    axi4_transfer_cfg_s        struct_cfg;

    `uvm_info(get_type_name(), $sformatf("DEBUG_MSHA :: Inside axi4_write_data"), UVM_NONE); 
   axi4_master_cfg_converter::from_class(axi4_master_agent_cfg_h, struct_cfg);
    axi4_master_mon_bfm_h.axi4_write_data_sampling(struct_write_packet,struct_cfg);
    axi4_master_seq_item_converter::to_write_class(struct_write_packet,req_wr);
  
    $cast(req_wr_clone_packet,req_wr.clone());
    `uvm_info(get_type_name(),$sformatf("Packet received from axi4_write_data_sampling is %p",req_wr.sprint()),UVM_HIGH)
    `uvm_info(get_type_name(),$sformatf("Packet received from axi4_write_data_sampling clone packet is %p",req_wr_clone_packet.sprint()),UVM_HIGH)
  end
endtask

task axi4_master_monitor_proxy::axi4_write_response();
//  forever begin
//    axi4_write_transfer_char_s struct_write_packet;
//    axi4_transfer_cfg_s        struct_cfg;
//
//    axi4_master_cfg_converter::from_class(axi4_master_agent_cfg_h, struct_cfg);
//    axi4_master_mon_bfm_h.axi4_write_response_sampling(struct_write_packet,struct_cfg);
//    axi4_master_seq_item_converter::to_write_class(struct_write_packet,req_wr);
//  end
endtask


task axi4_master_monitor_proxy::axi4_read_address();
 // forever begin
 //   axi4_read_transfer_char_s struct_read_packet;
 //   axi4_transfer_cfg_s        struct_cfg;

 //   axi4_master_cfg_converter::from_class(axi4_master_agent_cfg_h, struct_cfg);
 //   axi4_master_mon_bfm_h.axi4_read_address_sampling(struct_read_packet,struct_cfg);
 //   axi4_master_seq_item_converter::to_read_class(struct_read_packet,req_rd);
 // end
endtask

task axi4_master_monitor_proxy::axi4_read_data();
  forever begin
    axi4_read_transfer_char_s struct_read_packet;
    axi4_transfer_cfg_s       struct_cfg;
    axi4_master_tx            req_rd_clone_packet; 

    `uvm_info(get_type_name(), $sformatf("DEBUG :: Inside axi4_read_data"), UVM_NONE);
    
    axi4_master_cfg_converter::from_class(axi4_master_agent_cfg_h, struct_cfg);
    axi4_master_mon_bfm_h.axi4_read_data_sampling(struct_read_packet,struct_cfg);
    //`uvm_info(get_type_name(), $sformatf("DEBUG :: from BFM :: Read data %p ",struct_read_packet), UVM_NONE);
    axi4_master_seq_item_converter::to_read_class(struct_read_packet,req_rd);

    $cast(req_rd_clone_packet,req_rd.clone());
    `uvm_info(get_type_name(),$sformatf("Packet received from axi4_read_data_sampling is %p",req_rd.sprint()),UVM_HIGH)
    `uvm_info(get_type_name(),$sformatf("Packet received from axi4_read_data_sampling clone packet is %p",req_rd_clone_packet.sprint()),UVM_HIGH)

    axi4_master_read_data_analysis_port.write(req_rd);
  end
endtask

`endif

