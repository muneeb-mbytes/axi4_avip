`ifndef AXI4_MASTER_DRIVER_PROXY_INCLUDED_
`define AXI4_MASTER_DRIVER_PROXY_INCLUDED_

//--------------------------------------------------------------------------------------------
// Class: master_driver_proxy
//  Driver is written by extending uvm_driver,uvm_driver is inherited from uvm_component, 
//  Methods and TLM port (seq_item_port) are defined for communication between sequencer and driver,
//  uvm_driver is a parameterized class and it is parameterized with the type of the request 
//  sequence_item and the type of the response sequence_item 
//--------------------------------------------------------------------------------------------
class axi4_master_driver_proxy extends uvm_driver#(axi4_master_tx);
  `uvm_component_utils(axi4_master_driver_proxy)

  //Port: axi_write_seq_item_port
  //This port is used to request write items from the sequencer, they are also used it to send responses back.
  uvm_seq_item_pull_port #(REQ,RSP) axi_write_seq_item_port;
  
  //Port: axi_read_seq_item_port
  //This port is used to request read items from the sequencer, they are also used it to send responses back.
  uvm_seq_item_pull_port #(REQ,RSP) axi_read_seq_item_port;

  //Port: axi_write_rsp_port
  //This port provides an alternate way of sending responses back to the originating sequencer. 
  //Which port to use depends on which export the sequencer provides for connection.
  uvm_analysis_port #(RSP) axi_write_rsp_port;
  
  //Port: axi_read_rsp_port
  //This port provides an alternate way of sending responses back to the originating sequencer. 
  //Which port to use depends on which export the sequencer provides for connection.
  uvm_analysis_port #(RSP) axi_read_rsp_port;

  uvm_tlm_analysis_fifo #(axi4_master_tx) axi4_master_fifo_h;
  
  //Variable: req_wr, req_rd
  //Declaration of REQ handles
  REQ req_wr, req_rd;
  
  //Variable: rsp_wr, rsp_rd
  //Declaration of RSP handles
  RSP rsp_wr, rsp_rd;
      
  //Variable: axi4_master_agent_cfg_h
  //Declaring handle for axi4_master agent config class 
  axi4_master_agent_config axi4_master_agent_cfg_h;

  //Variable: axi4_master_drv_bfm_h
  //Declaring handle for axi4 driver bfm
  virtual axi4_master_driver_bfm axi4_master_drv_bfm_h;
  
  //-------------------------------------------------------
  // Externally defined Tasks and Functions
  //-------------------------------------------------------
  extern function new(string name = "axi4_master_driver_proxy", uvm_component parent = null);
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual function void end_of_elaboration_phase(uvm_phase phase);
  extern virtual task run_phase(uvm_phase phase);
  extern virtual task axi4_write_task();
  extern virtual task axi4_read_task();

endclass : axi4_master_driver_proxy

//--------------------------------------------------------------------------------------------
// Construct: new
//
// Parameters:
//  name - axi4_master_driver_proxy
//  parent - parent under which this component is created
//--------------------------------------------------------------------------------------------
function axi4_master_driver_proxy::new(string name = "axi4_master_driver_proxy", uvm_component parent = null);
  super.new(name, parent);
  axi_write_seq_item_port = new("axi_write_seq_item_port",this);
  axi_read_seq_item_port  = new("axi_read_seq_item_port",this);
  axi_write_rsp_port      = new("axi_write_rsp_port",this);
  axi_read_rsp_port       = new("axi_read_rsp_port",this);
  axi4_master_fifo_h      = new("axi4_master_fifo_h",this);
endfunction : new

//--------------------------------------------------------------------------------------------
// Function: build_phase
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
// Function: end_of_elaboration_phase
//
// Parameters:
//  phase - uvm phase
//--------------------------------------------------------------------------------------------
function void axi4_master_driver_proxy::end_of_elaboration_phase(uvm_phase phase);
  super.end_of_elaboration_phase(phase);
  axi4_master_drv_bfm_h.axi4_master_drv_proxy_h = this;
endfunction : end_of_elaboration_phase

//--------------------------------------------------------------------------------------------
// Task: run_phase
//  Gets the sequence_item, converts them to struct compatible transactions
//  and sends them to the BFM to drive the data over the interface
//
// Parameters:
//  phase - uvm phase
//--------------------------------------------------------------------------------------------
task axi4_master_driver_proxy::run_phase(uvm_phase phase);

  //waiting for system reset
  axi4_master_drv_bfm_h.wait_for_aresetn();

  fork 
    axi4_write_task();
    axi4_read_task();
  join

endtask : run_phase

//--------------------------------------------------------------------------------------------
// Task: axi4_write_task
//  Gets the sequence_item, converts them to struct compatible transactions
//  and sends them to the BFM to drive the data over the interface
//--------------------------------------------------------------------------------------------
task axi4_master_driver_proxy::axi4_write_task();
  forever begin
    axi4_master_tx local_master_tx;
    axi4_write_transfer_char_s struct_write_packet;
    axi4_transfer_cfg_s        struct_cfg;

    axi_write_seq_item_port.get_next_item(req_wr);
    `uvm_info(get_type_name(),$sformatf("DEBUG_SAHA_BEFORE::Sending_req_write_packet = \n %s",req_wr.sprint()),UVM_NONE); 

    //Converting configurations into struct config type
    axi4_master_cfg_converter::from_class(axi4_master_agent_cfg_h,struct_cfg);

    //Converting transactions into struct data type

    // MSHA: // put the req_wr into a FIFO/queue (depth must be equal to outstanding
    // MSHA: // transfers variable value )
    axi4_master_fifo_h.write(req_wr);

    // MSHA: //  Throw the error when we reach the limi
    `uvm_info(get_type_name(),$sformatf("DEBUG_SHW::Checking transfer type outside if= %s",req_wr.transfer_type),UVM_HIGH); 
    
    if(req_wr.transfer_type == BLOCKING_WRITE) begin
      //Calling 3 write tasks from axi4_master_drv_bfm in HDL side
      axi4_master_seq_item_converter::from_write_class(req_wr,struct_write_packet);
      `uvm_info(get_type_name(),$sformatf("DEBUG_SHW::Checking transfer type = %s",req_wr.transfer_type),UVM_HIGH); 
      axi4_master_drv_bfm_h.axi4_write_address_channel_task(struct_write_packet,struct_cfg);
      axi4_master_drv_bfm_h.axi4_write_data_channel_task(struct_write_packet,struct_cfg);
      axi4_master_drv_bfm_h.axi4_write_response_channel_task(struct_write_packet,struct_cfg);
    end

    else if(req_wr.transfer_type ==  NON_BLOCKING_WRITE) begin
      fork
        begin  
        `uvm_info(get_type_name(),$sformatf("DEBUG_SHW::Checking transfer type inside fork = %s",req_wr.transfer_type),UVM_HIGH); 
         // local_master_tx = axi4_master_fifo_h.peek();
          axi4_master_fifo_h.peek(local_master_tx);
          `uvm_info(get_type_name(),$sformatf("DEBUG_SHW::Checking local master tx = %s",local_master_tx.sprint()),UVM_HIGH); 
          axi4_master_seq_item_converter::from_write_class(local_master_tx,struct_write_packet);
          `uvm_info(get_type_name(),$sformatf("DEBUG_SHW::Checking struct packet = %p",struct_write_packet),UVM_HIGH); 
          axi4_master_drv_bfm_h.axi4_write_address_channel_task(struct_write_packet,struct_cfg);
        end
    
        begin
          //local_master_tx = axi4_master_fifo_h.peek();
          axi4_master_fifo_h.peek(local_master_tx);
          axi4_master_seq_item_converter::from_write_class(local_master_tx,struct_write_packet);
          axi4_master_drv_bfm_h.axi4_write_data_channel_task(struct_write_packet,struct_cfg);
        end
     
        begin
           //local_master_tx = axi4_master_fifo_h.peek();
           axi4_master_fifo_h.peek(local_master_tx);
           axi4_master_seq_item_converter::from_write_class(local_master_tx,struct_write_packet);
           axi4_master_drv_bfm_h.axi4_write_response_channel_task(struct_write_packet,struct_cfg);
        end
        //local_master_tx = axi4_master_fifo_h.get();

      join_any
        axi4_master_fifo_h.get(local_master_tx);
    end
    // MSHA:     // struct_packet_local = FIFO.peek();
    // MSHA:     ADD(struct_packet)
    // MSHA:     // struct_packet_local = FIFO.peek();
    // MSHA:     DATA(struct_packet)
    // MSHA:     // struct_packet_local = FIFO.peek();
    // MSHA:     RES(struct_packet)
    // MSHA:     //pop the element and display the current outstanding value
    // MSHA:   join_any
    // MSHA: end

    //Calling 3 write tasks from axi4_master_drv_bfm in HDL side
    // axi4_master_drv_bfm_h.axi4_write_address_channel_task(struct_write_packet,struct_cfg);
     //axi4_master_drv_bfm_h.axi4_write_data_channel_task(struct_write_packet,struct_cfg);
    //    axi4_master_drv_bfm_h.axi4_write_response_channel_task(struct_write_packet,struct_cfg);
  
    // MSHA: fork
    // MSHA:   axi4_master_drv_bfm_h.axi4_write_address_channel_task(struct_write_packet,struct_cfg);
    // MSHA:   axi4_master_drv_bfm_h.axi4_write_data_channel_task(struct_write_packet,struct_cfg);
    // MSHA:   axi4_master_drv_bfm_h.axi4_write_response_channel_task(struct_write_packet,struct_cfg);
    // MSHA: join_any
    
    //Converting transactions into struct data type
    axi4_master_seq_item_converter::to_write_class(struct_write_packet,req_wr);

    `uvm_info(get_type_name(),$sformatf("DEBUG_SAHA_AFTER::Received_req_write_packet = \n %s",req_wr.sprint()),UVM_NONE);

    axi_write_seq_item_port.item_done();
  end
endtask : axi4_write_task


//--------------------------------------------------------------------------------------------
// Task: axi4_read_task
//  Gets the sequence_item, converts them to struct compatible transactions
//  and sends them to the BFM to drive the data over the interface
//--------------------------------------------------------------------------------------------
task axi4_master_driver_proxy::axi4_read_task();
  forever begin
    axi4_read_transfer_char_s struct_read_packet;
    axi4_transfer_cfg_s       struct_cfg;

    axi_read_seq_item_port.get_next_item(req_rd);
    `uvm_info(get_type_name(),$sformatf("DEBUG_SAHA_BEFORE::Sending_req_read_packet = \n %s",req_rd.sprint()),UVM_NONE); 

    //Converting transactions into struct data type
    axi4_master_seq_item_converter::from_read_class(req_rd,struct_read_packet);

    //Converting configurations into struct config type
    axi4_master_cfg_converter::from_class(axi4_master_agent_cfg_h,struct_cfg);

    //Calling 2 read channel tasks from axi4_master_drv_bfm in HDL side
    axi4_master_drv_bfm_h.axi4_read_address_channel_task(struct_read_packet,struct_cfg);
    axi4_master_drv_bfm_h.axi4_read_data_channel_task(struct_read_packet,struct_cfg);
    
    //Converting transactions into struct data type
    axi4_master_seq_item_converter::to_read_class(struct_read_packet,req_rd);

    `uvm_info(get_type_name(),$sformatf("DEBUG_SAHA_AFTER::Received_req_read_packet = \n %s",req_rd.sprint()),UVM_NONE);

    axi_read_seq_item_port.item_done();
  end
endtask : axi4_read_task

`endif

