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
  // Derived driver classes should use this port to request items from the sequencer
  // They may also use it to send responses back.
  
  uvm_seq_item_pull_port #(REQ, RSP) axi_write_seq_item_port;
  uvm_seq_item_pull_port #(REQ, RSP) axi_read_seq_item_port;

  // Port: rsp_port
  // This port provides an alternate way of sending responses back to the originating sequencer.
  // Which port to use depends on which export the sequencer provides for connection.
  
  uvm_analysis_port #(RSP) axi_write_rsp_port;
  uvm_analysis_port #(RSP) axi_read_rsp_port;
  
  REQ req_wr, req_rd;
  RSP rsp_wr, rsp_rd;

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
  extern virtual task axi4_write_task();
  extern virtual task axi4_read_task();

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
  
  //wait for system reset
  axi4_slave_drv_bfm_h.wait_for_system_reset();

  fork 
    axi4_write_task();
    axi4_read_task();
  join

  //  axi4_write_transfer_char_s struct_write_packet_char;
  //  axi4_read_transfer_char_s struct_read_packet_char;
  //  axi4_transfer_cfg_s    struct_cfg;

  //  //seq_item_port.get_next_item(req);
  //  axi_write_task();
  //  axi_read_task();
  //  axi4_slave_seq_item_converter::from_write_class(req,struct_write_packet_char);
  //  axi4_slave_seq_item_converter::from_read_class(req,struct_read_packet_char);
  //  axi4_slave_cfg_converter::from_class(axi4_slave_agent_cfg_h,struct_cfg);


  //  axi4_slave_seq_item_converter::to_write_class(struct_write_packet_char,req);
  //  axi4_slave_seq_item_converter::to_read_class(struct_read_packet_char,req);
    //axi4_slave_cfg_converter::to_class(struct_cfg,axi4_slave_agent_cfg_h);

endtask : run_phase 

//--------------------------------------------------------------------------------------------
// task axi4 write task
//--------------------------------------------------------------------------------------------
task axi4_slave_driver_proxy::axi4_write_task();

  forever begin
    axi4_write_transfer_char_s struct_write_packet;
    axi4_transfer_cfg_s       struct_cfg;

    axi_write_seq_item_port.get_next_item(req_wr);
    //`uvm_info(get_type_name(), $sformatf("DEBUG_MSHA :: slave_req_wr = \n%s",req_wr.sprint()), UVM_NONE); 
    

    // 1. wait for address (put into the fifo only when the outstadning value is less than the
    // FIFO size - throw error when u have reached the limit) 
    // 1. wait for data (combine data with address (peek)info to make a packet - then come with response) 
    //    1.a driving my response (throw away the FIFO value)


    if(req_wr.transfer_type == BLOCKING_WRITE) begin
   
      //Converting transactions into struct data type
      axi4_slave_seq_item_converter::from_write_class(req_wr,struct_write_packet);
      `uvm_info(get_type_name(), $sformatf("from_write_class:: struct_write_packet = \n %0p",struct_write_packet), UVM_HIGH); 

      //Converting configurations into struct config type
      axi4_slave_cfg_converter::from_class(axi4_slave_agent_cfg_h,struct_cfg);
      `uvm_info(get_type_name(), $sformatf("from_write_class:: struct_cfg =  \n %0p",struct_cfg),UVM_HIGH); 

      //write address_task
      axi4_slave_drv_bfm_h.axi4_write_address_phase(struct_write_packet);
    
      // write data_task
      axi4_slave_drv_bfm_h.axi4_write_data_phase(struct_write_packet,struct_cfg);

      // write response_task
      axi4_slave_drv_bfm_h.axi4_write_response_phase(struct_write_packet,struct_cfg);
    end

    if(req_wr.transfer_type ==  NON_BLOCKING_WRITE) begin
      
      fork
        `uvm_info("SEQ_DEBUG", $sformatf("seq =  \n %0p",req_wr.sprint()),UVM_HIGH);
        
        //Converting transactions into struct data type
        axi4_slave_seq_item_converter::from_write_class(req_wr,struct_write_packet);
        `uvm_info(get_type_name(), $sformatf("from_write_class:: struct_write_packet = \n %0p",struct_write_packet), UVM_HIGH); 
        
        //Converting configurations into struct config type
        axi4_slave_cfg_converter::from_class(axi4_slave_agent_cfg_h,struct_cfg);
        `uvm_info(get_type_name(), $sformatf("from_write_class:: struct_cfg =  \n %0p",struct_cfg),UVM_HIGH); 
        
        //write address_task
        axi4_slave_drv_bfm_h.axi4_write_address_phase(struct_write_packet);
        
        // write data_task
        axi4_slave_drv_bfm_h.axi4_write_data_phase(struct_write_packet,struct_cfg);
      join
      
      // write response_task
      axi4_slave_drv_bfm_h.axi4_write_response_phase(struct_write_packet,struct_cfg);
    end

    #10;

    //Converting transactions into struct data type
    axi4_slave_seq_item_converter::to_write_class(struct_write_packet,req_wr);

   // `uvm_info("DEBUG_MSHA", $sformatf("AFTER :: Received req packet \n %s", req_wr.sprint()), UVM_NONE);

    axi_write_seq_item_port.item_done();
  end

endtask : axi4_write_task

//-------------------------------------------------------
// task axi4 read task
//-------------------------------------------------------
task axi4_slave_driver_proxy::axi4_read_task();

  forever begin
    axi4_read_transfer_char_s struct_read_packet;
    axi4_transfer_cfg_s       struct_cfg;

    axi_read_seq_item_port.get_next_item(req_rd);
    
    if(req_rd.transfer_type == BLOCKING_READ) begin
  
      //Converting transactions into struct data type
      axi4_slave_seq_item_converter::from_read_class(req_rd,struct_read_packet);
      `uvm_info(get_type_name(), $sformatf("from_read_class:: struct_read_packet = \n %0p",struct_read_packet), UVM_HIGH);
      
      //Converting configurations into struct config type
      axi4_slave_cfg_converter::from_class(axi4_slave_agent_cfg_h,struct_cfg);
      `uvm_info(get_type_name(), $sformatf("from_read_class:: struct_cfg = \n %0p",struct_cfg), UVM_HIGH); 

      //read address task
      axi4_slave_drv_bfm_h.axi4_read_address_phase(struct_read_packet,struct_cfg);
    
      //read response task
      axi4_slave_drv_bfm_h.axi4_read_data_phase(struct_read_packet,struct_cfg);
    
    end
    
    else if(req_rd.transfer_type == NON_BLOCKING_READ) begin
      
      fork
        
        //Converting transactions into struct data type
        axi4_slave_seq_item_converter::from_read_class(req_rd,struct_read_packet);
        `uvm_info(get_type_name(), $sformatf("from_read_class:: struct_read_packet = \n %0p",struct_read_packet), UVM_HIGH);
      
        //Converting configurations into struct config type
        axi4_slave_cfg_converter::from_class(axi4_slave_agent_cfg_h,struct_cfg);
        `uvm_info(get_type_name(), $sformatf("from_read_class:: struct_cfg = \n %0p",struct_cfg), UVM_HIGH); 

        //read address task
        axi4_slave_drv_bfm_h.axi4_read_address_phase(struct_read_packet,struct_cfg);
    
        //read response task
        axi4_slave_drv_bfm_h.axi4_read_data_phase(struct_read_packet,struct_cfg);

      join_any
    
    end

    
    //Converting struct into transactions
    axi4_slave_seq_item_converter::to_read_class(struct_read_packet,req_rd);

    //`uvm_info("DEBUG_MSHA", $sformatf("AFTER :: Received req packet \n %s", req_rd.sprint()), UVM_NONE);
  
    #10;

    axi_read_seq_item_port.item_done();
  end
endtask : axi4_read_task

`endif
