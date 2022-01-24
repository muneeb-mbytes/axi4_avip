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

  //Variable: axi4_master_fifo_h
  //Declaring handle for uvm_tlm_analysis_fifo
  uvm_tlm_analysis_fifo #(axi4_slave_tx) axi4_slave_write_fifo_h;
  uvm_tlm_analysis_fifo #(axi4_slave_tx) axi4_slave_read_fifo_h;
  
  //-------------------------------------------------------
  // Externally defined Tasks and Functions
  //-------------------------------------------------------
  extern function new(string name = "axi4_slave_driver_proxy", uvm_component parent = null);
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual function void end_of_elaboration_phase(uvm_phase phase);
  extern virtual task run_phase(uvm_phase phase);
  extern virtual task axi4_write_task();
  extern virtual task axi4_read_task();
 // extern virtual task check_for_slave_resp(inout axi4_write_transfer_char_s struct_write_packet
 // axi4_read_transfer_char_s struct_read_packet);
 // extern virtual task task_memory_write(inout axi4_write_transfer_char_s struct_write_packet);
 // extern virtual task task_memory_read(inout axi4_read_transfer_char_s struct_read_packet);
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
  axi4_slave_write_fifo_h    = new("axi4_slave_write_fifo_h",this);
  axi4_slave_read_fifo_h     = new("axi4_slave_read_fifo_h",this);
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

endtask : run_phase 

//--------------------------------------------------------------------------------------------
// task axi4 write task
//--------------------------------------------------------------------------------------------
task axi4_slave_driver_proxy::axi4_write_task();

  forever begin
      
    axi4_slave_tx              local_slave_tx;
    axi4_write_transfer_char_s struct_write_packet;
    axi4_transfer_cfg_s        struct_cfg;

    axi_write_seq_item_port.get_next_item(req_wr);
    //`uvm_info(get_type_name(), $sformatf("DEBUG_MSHA :: slave_req_wr = \n%s",req_wr.sprint()), UVM_NONE); 
//    process addr_tx;
    fork
    begin
  //    addr_tx=process::self();
      axi4_slave_tx              local_slave_addr_tx;
      axi4_write_transfer_char_s struct_write_packet;
      axi4_transfer_cfg_s        struct_cfg;
    
      //Converting transactions into struct data type
      axi4_slave_seq_item_converter::from_write_class(req_wr,struct_write_packet);
     `uvm_info(get_type_name(), $sformatf("from_write_class:: struct_write_packet = \n %0p",struct_write_packet), UVM_HIGH); 

     //Converting configurations into struct config type
     axi4_slave_cfg_converter::from_class(axi4_slave_agent_cfg_h,struct_cfg);
     `uvm_info(get_type_name(), $sformatf("from_write_class:: struct_cfg =  \n %0p",struct_cfg),UVM_HIGH);
      
      //write address_task
      axi4_slave_drv_bfm_h.axi4_write_address_phase(struct_write_packet);
    
      //Converting struct into transaction data type
     axi4_slave_seq_item_converter::to_write_class(struct_write_packet,local_slave_addr_tx);

    `uvm_info("DEBUG_SLAVE_WRITE_ADDR_PROXY", $sformatf("AFTER :: Received req packet \n %s",local_slave_addr_tx.sprint()), UVM_NONE);
    
    axi4_slave_write_fifo_h.write(local_slave_addr_tx);

    end 
   begin
      axi4_slave_tx              local_slave_addr_tx;
      axi4_slave_tx              local_slave_data_tx;
      axi4_write_transfer_char_s struct_write_packet;
      axi4_transfer_cfg_s        struct_cfg;
      axi4_slave_tx                 packet;
    
      //Converting transactions into struct data type
      axi4_slave_seq_item_converter::from_write_class(req_wr,struct_write_packet);
      `uvm_info(get_type_name(), $sformatf("from_write_class:: struct_write_packet = \n %0p",struct_write_packet), UVM_HIGH); 

      //Converting configurations into struct config type
      axi4_slave_cfg_converter::from_class(axi4_slave_agent_cfg_h,struct_cfg);
      `uvm_info(get_type_name(), $sformatf("from_write_class:: struct_cfg =  \n %0p",struct_cfg),UVM_HIGH);

      // write data_task
      axi4_slave_drv_bfm_h.axi4_write_data_phase(struct_write_packet,struct_cfg);
      `uvm_info("DEBUG_SLAVE_WDATA_PROXY", $sformatf("AFTER :: sending struct pkt to bfm \n %p",struct_write_packet), UVM_HIGH);
      
      //Converting struct into transaction data type
      axi4_slave_seq_item_converter::to_write_class(struct_write_packet,local_slave_data_tx);

     `uvm_info("DEBUG_SLAVE_WDATA_PROXY_TO_CLASS", $sformatf("AFTER TO CLASS :: Received req packet \n %s", local_slave_data_tx.sprint()), UVM_NONE);

     axi4_slave_write_fifo_h.peek(local_slave_addr_tx);
    `uvm_info("DEBUG_SLAVE_WDATA_PROXY_FIFO", $sformatf("AFTER :: Received FIFO packet \n %s",local_slave_addr_tx.sprint()), UVM_HIGH);
    
     // axi4_slave_seq_item_converter::tx_packet(local_slave_addr_tx,local_slave_data_tx,packet);
     //  `uvm_info("DEBUG_SLAVE_WDATA_PROXY_FIFO", $sformatf("AFTER :: COMBINED packet \n %s",packet.sprint()), UVM_HIGH);

      // $cast(local_slave_tx,local_slave_tx.clone());
      //  `uvm_info("DEBUG_SLAVE_WDATA_PROXY_PACKED", $sformatf("AFTER :: Packed Packet \n %s",local_slave_tx.sprint()), UVM_HIGH);

    end
  
  join 
    
    // write response_task
    axi4_slave_drv_bfm_h.axi4_write_response_phase(struct_write_packet,struct_cfg);
  //  axi4_slave_write_fifo_h.get(local_slave_tx);
    #10;


    axi_write_seq_item_port.item_done();
  end

endtask : axi4_write_task

//-------------------------------------------------------
// task axi4 read task
//-------------------------------------------------------
task axi4_slave_driver_proxy::axi4_read_task();

  forever begin
    
    axi4_slave_tx              local_slave_tx;
    axi4_read_transfer_char_s struct_read_packet;
    axi4_transfer_cfg_s       struct_cfg;

    axi_read_seq_item_port.get_next_item(req_rd);
    

    //Converting transactions into struct data type
    axi4_slave_seq_item_converter::from_read_class(req_rd,struct_read_packet);
   `uvm_info(get_type_name(), $sformatf("from_read_class:: struct_read_packet = \n %0p",struct_read_packet), UVM_HIGH); 
 
   //Converting configurations into struct config type
   axi4_slave_cfg_converter::from_class(axi4_slave_agent_cfg_h,struct_cfg);
   `uvm_info(get_type_name(), $sformatf("from_read_class:: struct_cfg =  \n %0p",struct_cfg),UVM_HIGH);
    
    //read address_task
    axi4_slave_drv_bfm_h.axi4_read_address_phase(struct_read_packet,struct_cfg);
  
    //Converting struct into transaction data type
   axi4_slave_seq_item_converter::to_read_class(struct_read_packet,local_slave_tx);
 
  `uvm_info("DEBUG_SLAVE_READ_ADDR_PROXY", $sformatf("AFTER :: Received req packet \n %s",local_slave_tx.sprint()), UVM_NONE);
 
   axi4_slave_read_fifo_h.put(local_slave_tx);
 
  `uvm_info("DEBUG_SLAVE_READ_ADDR_FIFO", $sformatf("AFTER :: Received req packet \n %s",local_slave_tx.sprint()), UVM_NONE);
 

   //read data task
   axi4_slave_drv_bfm_h.axi4_read_data_phase(struct_read_packet,struct_cfg);

    axi4_slave_read_fifo_h.get(local_slave_tx);
   // fork
   //   
   //   //Converting transactions into struct data type
   //   axi4_slave_seq_item_converter::from_read_class(req_rd,struct_read_packet);
   //   `uvm_info(get_type_name(), $sformatf("from_read_class:: struct_read_packet = \n %0p",struct_read_packet), UVM_HIGH);
   //   
   //   //Converting configurations into struct config type
   //   axi4_slave_cfg_converter::from_class(axi4_slave_agent_cfg_h,struct_cfg);
   //   `uvm_info(get_type_name(), $sformatf("from_read_class:: struct_cfg = \n %0p",struct_cfg), UVM_HIGH); 
   //   
   //   //read address task
   //   axi4_slave_drv_bfm_h.axi4_read_address_phase(struct_read_packet,struct_cfg);
   //   
   //   //read response task
   //   axi4_slave_drv_bfm_h.axi4_read_data_phase(struct_read_packet,struct_cfg);
   // 
   // join_any
   //   
   // //Converting struct into transactions
   // axi4_slave_seq_item_converter::to_read_class(struct_read_packet,req_rd);
    //`uvm_info("DEBUG_MSHA", $sformatf("AFTER :: Received req packet \n %s", req_rd.sprint()), UVM_NONE);
  
    #10;

    axi_read_seq_item_port.item_done();
  end

endtask : axi4_read_task

//--------------------------------------------------------------------------------------------
// Task: task_memory_write
// This task is used to write the data into the slave memory
// Parameters:
//  struct_packet   - axi4_write_transfer_char_s
//--------------------------------------------------------------------------------------------

//task task_memory_write(inout axi4_write_transfer_char_s struct_write_packet);
//  `uvm_info("DEBUG_MEMORY_WRITE", $sformatf("task_memory_write"), UVM_HIGH); 
//  for(int i=0; i<(DATA_WIDTH/8); i++)begin
//    `uvm_info("DEBUG_MEMORY_WRITE", $sformatf("task_memory_write inside for loop :: %0d", i), UVM_HIGH);
//    //`uvm_info("DEBUG_MEMORY_WRITE", $sformatf("task_memory_write inside for loop wstrb = %0b", struct_packet.pstrb[i]), UVM_HIGH);
//    //if(struct_write_packet.wstrb[i] == 1)begin
//    axi4_slave_agent_cfg_h.slave_memory_task(struct_write_packet.awaddr+i,struct_write_packet.wdata[8*i+7 -: 8]);
//    `uvm_info("DEBUG_NA", $sformatf("task_memory_write inside for loop data = %0h", 
//                                      axi4_slave_agent_cfg_h.slave_memory[struct_write_packet.awddr+i]), UVM_HIGH);
//    end
//  //end
//endtask : task_memory_write

//--------------------------------------------------------------------------------------------
// Task: task_memory_read
// This task is used to read the data from the slave memory
// Parameters:
//  struct_packet   - axi4_read_transfer_char_s
//--------------------------------------------------------------------------------------------

//task task_memory_read(inout axi4_read_transfer_char_s struct_read_packet);
// `uvm_info("DEBUG_MEMORY_READ", $sformatf("task_memory_read"), UVM_HIGH);
//  for(int i=0; i<(DATA_WIDTH/8); i++)begin
//    if(axi4_slave_agent_cfg_h.slave_memory.exists(struct_read_packet.arddr))begin
//      struct_raed_packet.rdata[8*i+7 -: 8] =
//      axi4_slave_agent_cfg_h.slave_memory[struct_read_packet.arddr + i];
//    end
//    else begin
//      `uvm_error(get_type_name(), $sformatf("Selected address has no data"));
//      struct_read_packet.rresp = READ_DECERR;
//      struct_read_packet.rdata  = 'h0;
//    end
//  end 
//endtask : task_memory_read
  

`endif
