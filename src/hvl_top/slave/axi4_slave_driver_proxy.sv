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

  //Declaring handle for uvm_tlm_analysis_fifo's for all the five channels
  uvm_tlm_fifo #(axi4_slave_tx) axi4_slave_write_addr_fifo_h;
  uvm_tlm_fifo #(axi4_slave_tx) axi4_slave_write_data_in_fifo_h;
  uvm_tlm_fifo #(axi4_slave_tx) axi4_slave_write_response_fifo_h;
  uvm_tlm_fifo #(axi4_slave_tx) axi4_slave_write_data_out_fifo_h;
  uvm_tlm_fifo #(axi4_slave_tx) axi4_slave_read_addr_fifo_h;
  uvm_tlm_fifo #(axi4_slave_tx) axi4_slave_read_data_in_fifo_h;

  //Declaring Semaphore handles for writes and reads
  semaphore semaphore_write_key;
  semaphore semaphore_read_key;
  
  //-------------------------------------------------------
  // Externally defined Tasks and Functions
  //-------------------------------------------------------
  extern function new(string name = "axi4_slave_driver_proxy", uvm_component parent = null);
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual function void end_of_elaboration_phase(uvm_phase phase);
  extern virtual task run_phase(uvm_phase phase);
  extern virtual task axi4_write_task();
  extern virtual task axi4_read_task();
  extern virtual task task_memory_write(inout axi4_slave_tx struct_write_packet);
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
  axi_write_seq_item_port                   = new("axi_write_seq_item_port", this);
  axi_read_seq_item_port                    = new("axi_read_seq_item_port", this);
  axi_write_rsp_port                        = new("axi_write_rsp_port", this);
  axi_read_rsp_port                         = new("axi_read_rsp_port", this);
  axi4_slave_write_addr_fifo_h              = new("axi4_slave_write_addr_fifo_h",this,16);
  axi4_slave_write_data_in_fifo_h           = new("axi4_slave_write_data_in_fifo_h",this,16);
  axi4_slave_write_response_fifo_h          = new("axi4_slave_write_response_fifo_h",this,16);
  axi4_slave_write_data_out_fifo_h          = new("axi4_slave_write_data_out_fifo_h",this,16);
  axi4_slave_read_addr_fifo_h               = new("axi4_slave_read_addr_fifo_h",this,16);
  axi4_slave_read_data_in_fifo_h            = new("axi4_slave_read_data_in_fifo_h",this,16);
  semaphore_write_key                       = new(1);
  semaphore_read_key                        = new(1);
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
    
    process addr_tx;
    process data_tx;
    process response_tx;

    axi_write_seq_item_port.get_next_item(req_wr);

    // writting the req into write data and response fifo's
    axi4_slave_write_data_in_fifo_h.put(req_wr);
    axi4_slave_write_response_fifo_h.put(req_wr);
    
    fork
    begin : WRITE_ADDRESS_CHANNEL
      
      axi4_slave_tx              local_slave_addr_tx;
      axi4_write_transfer_char_s struct_write_packet;
      axi4_transfer_cfg_s        struct_cfg;
    
      //returns status of address thread
      addr_tx=process::self();
      
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
     
     // putting write address data into address fifo
     if(axi4_slave_write_addr_fifo_h.is_full) begin
       `uvm_error(get_type_name(),$sformatf("WRITE_ADDR_THREAD::Cannot put into FIFO as WRITE_FIFO is FULL"));
     end
     else begin
       axi4_slave_write_addr_fifo_h.put(local_slave_addr_tx);
     end
   
   end
 
  begin : WRITE_DATA_CHANNEL

      axi4_slave_tx              local_slave_data_tx;
      axi4_write_transfer_char_s struct_write_packet;
      axi4_transfer_cfg_s        struct_cfg;
      
      //returns status of write data thread
      data_tx=process::self();

      // Trying to get the write key 
      semaphore_write_key.get(1);

      //getting the data from write data fifo
      axi4_slave_write_data_in_fifo_h.get(local_slave_data_tx);
      
      //Converting transactions into struct data type
      axi4_slave_seq_item_converter::from_write_class(local_slave_data_tx,struct_write_packet);
      `uvm_info(get_type_name(), $sformatf("from_write_class:: struct_write_packet = \n %0p",struct_write_packet), UVM_HIGH); 

      //Converting configurations into struct config type
      axi4_slave_cfg_converter::from_class(axi4_slave_agent_cfg_h,struct_cfg);
      `uvm_info(get_type_name(), $sformatf("from_write_class:: struct_cfg =  \n %0p",struct_cfg),UVM_HIGH);

      // write data_task
      axi4_slave_drv_bfm_h.axi4_write_data_phase(struct_write_packet,struct_cfg);
      `uvm_info("DEBUG_SLAVE_WDATA_PROXY", $sformatf("AFTER :: Reciving struct pkt from bfm \n %p",struct_write_packet), UVM_HIGH);
     
      
      //Converting struct into transaction data type
      axi4_slave_seq_item_converter::to_write_class(struct_write_packet,local_slave_data_tx);

     `uvm_info("DEBUG_SLAVE_WDATA_PROXY_TO_CLASS", $sformatf("AFTER TO CLASS :: Received req packet \n %s", local_slave_data_tx.sprint()), UVM_NONE);

     //putting the write data into write dat out fifo 
      axi4_slave_write_data_out_fifo_h.put(local_slave_data_tx);

      //putting back the semaphore key
      semaphore_write_key.put(1);
    
    end
  
  begin : WRITE_RESPONSE_CHANNEL

      axi4_slave_tx              local_slave_addr_tx;
      axi4_slave_tx              local_slave_data_tx;
      axi4_slave_tx              local_slave_response_tx;
      axi4_slave_tx              packet;
      axi4_write_transfer_char_s struct_write_packet;
      axi4_transfer_cfg_s        struct_cfg;
      
      //returns status of response thread
      response_tx=process::self();

      //getting the key from semaphore 
      semaphore_write_key.get(1);

      //getting the data from response fifo
      axi4_slave_write_response_fifo_h.get(local_slave_response_tx);
      
      //Converting transactions into struct data type
      axi4_slave_seq_item_converter::from_write_class(local_slave_response_tx,struct_write_packet);
      `uvm_info(get_type_name(), $sformatf("from_write_class:: struct_write_packet = \n %0p",struct_write_packet), UVM_HIGH); 

      //Converting configurations into struct config type
      axi4_slave_cfg_converter::from_class(axi4_slave_agent_cfg_h,struct_cfg);
      `uvm_info(get_type_name(), $sformatf("from_write_class:: struct_cfg =  \n %0p",struct_cfg),UVM_HIGH);

      // write response_task
      axi4_slave_drv_bfm_h.axi4_write_response_phase(struct_write_packet,struct_cfg);
      `uvm_info("DEBUG_SLAVE_WDATA_PROXY", $sformatf("AFTER :: Reciving struct pkt from bfm \n %p",struct_write_packet), UVM_HIGH);
      
      //Converting struct into transaction data type
      axi4_slave_seq_item_converter::to_write_class(struct_write_packet,local_slave_response_tx);

     `uvm_info("DEBUG_SLAVE_WDATA_PROXY_TO_CLASS", $sformatf("AFTER TO CLASS :: Received req packet \n %s", local_slave_response_tx.sprint()), UVM_NONE);
     
     //check for fifo empty if not get the data 
     if(axi4_slave_write_addr_fifo_h.is_empty) begin
       `uvm_error(get_type_name(),$sformatf("WRITE_RESP_THREAD::Cannot get write addr data from FIFO as WRITE_ADDR_FIFO is EMPTY"));
     end
     else begin
      axi4_slave_write_addr_fifo_h.get(local_slave_addr_tx);
      `uvm_info("DEBUG_FIFO",$sformatf("fifo_size = %0d",axi4_slave_write_addr_fifo_h.size()),UVM_HIGH)
      `uvm_info("DEBUG_FIFO",$sformatf("fifo_used = %0d",axi4_slave_write_addr_fifo_h.used()),UVM_HIGH)
    end

      axi4_slave_write_data_out_fifo_h.get(local_slave_data_tx);

     //Calling combined data packet from converter class
     axi4_slave_seq_item_converter::tx_write_packet(local_slave_addr_tx,local_slave_data_tx,local_slave_response_tx,packet);
     `uvm_info("DEBUG_SLAVE_WDATA_PROXY", $sformatf("AFTER :: COMBINED WRITE CHANNEL PACKET \n %s",packet.sprint()), UVM_HIGH);

     //calling task memory write to store the data into slave memory
     task_memory_write(packet);

     //putting back the key
     semaphore_write_key.put(1);
   end
  
  join_any

  //checking the status of write address thread
  addr_tx.await();
  `uvm_info("SLAVE_STATUS_CHECK",$sformatf("AFTER_FORK_JOIN_ANY:: SLAVE_ADDRESS_CHANNEL_STATUS = \n %s",addr_tx.status()),UVM_MEDIUM)
  `uvm_info("SLAVE_STATUS_CHECK",$sformatf("AFTER_FORK_JOIN_ANY:: SLAVE_WDATA_CHANNEL_STATUS = \n %s",data_tx.status()),UVM_MEDIUM)
  `uvm_info("SLAVE_STATUS_CHECK",$sformatf("AFTER_FORK_JOIN_ANY:: SLAVE_WRESP_CHANNEL_STATUS = \n %s",response_tx.status()),UVM_MEDIUM)
   
   axi_write_seq_item_port.item_done();
 end
 
 endtask : axi4_write_task

//-------------------------------------------------------
// task axi4 read task
//-------------------------------------------------------
task axi4_slave_driver_proxy::axi4_read_task();
  
  forever begin
    
    //Declaring the process for read address channel and read data channel for status check 
    process rd_addr;
    process rd_data;

    axi_read_seq_item_port.get_next_item(req_rd);

    //putting the data into read data fifo
    axi4_slave_read_data_in_fifo_h.put(req_rd);

    fork
    begin : READ_ADDRESS_CHANNEL
      
      axi4_slave_tx              local_slave_tx;
      axi4_read_transfer_char_s struct_read_packet;
      axi4_transfer_cfg_s       struct_cfg;
      
      //returns status of address thread
      rd_addr = process::self();
      
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
      `uvm_info("DEBUG_SLAVE_READ_ADDR_PROXY", $sformatf(" to_class_raddr_phase_slave_proxy  \n %p",struct_read_packet), UVM_NONE);
     
      //Putting back the sampled read address data into fifo
      axi4_slave_read_addr_fifo_h.put(local_slave_tx);
      `uvm_info("DEBUG_SLAVE_READ_ADDR_PROXY", $sformatf("AFTER :: Received req packet \n %s",local_slave_tx.sprint()), UVM_NONE);
    
    end
  
   begin : READ_DATA_CHANNEL
    
     axi4_slave_tx              local_slave_rdata_tx;
     axi4_slave_tx              local_slave_raddr_tx;
     axi4_slave_tx              packet;
     axi4_read_transfer_char_s struct_read_packet;
     axi4_transfer_cfg_s       struct_cfg;

     //returns status of data thread
     rd_data = process::self();

     //Getting the key from semaphore
     semaphore_read_key.get(1);

     //Waiting for the read address thread to complete
     rd_addr.await();

     //Getting the data from read data fio
     axi4_slave_read_data_in_fifo_h.get(local_slave_rdata_tx);

     //Converting transactions into struct data type
     axi4_slave_seq_item_converter::from_read_class(local_slave_rdata_tx,struct_read_packet);
     `uvm_info(get_type_name(), $sformatf("from_read_class:: struct_read_packet = \n %0p",struct_read_packet), UVM_HIGH); 
 
     //Converting configurations into struct config type
     axi4_slave_cfg_converter::from_class(axi4_slave_agent_cfg_h,struct_cfg);
     `uvm_info(get_type_name(), $sformatf("from_read_class:: struct_cfg =  \n %0p",struct_cfg),UVM_HIGH);
     
     //read data task
     axi4_slave_drv_bfm_h.axi4_read_data_phase(struct_read_packet,struct_cfg);
     `uvm_info("DEBUG_SLAVE_RDATA_PROXY", $sformatf("AFTER :: READ CHANNEL PACKET \n %p",struct_read_packet), UVM_HIGH);

     //Calling converter class for reads to convert struct to req
     axi4_slave_seq_item_converter::to_read_class(struct_read_packet,local_slave_rdata_tx);
     `uvm_info("DEBUG_SLAVE_RDATA_PROXY", $sformatf("AFTER :: READ CHANNEL PACKET \n %s",local_slave_rdata_tx.sprint()), UVM_HIGH);

     //Getting teh sampled read address from read address fifo
     axi4_slave_read_addr_fifo_h.get(local_slave_raddr_tx);
    
     //Calling the Combined coverter class to combine read address and read data packet
     axi4_slave_seq_item_converter::tx_read_packet(local_slave_raddr_tx,local_slave_rdata_tx,packet);
     `uvm_info("DEBUG_SLAVE_RDATA_PROXY", $sformatf("AFTER :: COMBINED READ CHANNEL PACKET \n %s",packet.sprint()), UVM_HIGH);
     
     //Putting back the key
     semaphore_read_key.put(1);
   end
  join_any
 
  //Check the status of read address thread
  rd_addr.await();
  `uvm_info("SLAVE_STATUS_CHECK",$sformatf("AFTER_FORK_JOIN_ANY:: SLAVE_READ_CHANNEL_STATUS = \n %s",rd_addr.status()),UVM_MEDIUM)
  `uvm_info("SLAVE_STATUS_CHECK",$sformatf("AFTER_FORK_JOIN_ANY:: SLAVE_RDATA_CHANNEL_STATUS = \n %s",rd_data.status()),UVM_MEDIUM)

  axi_read_seq_item_port.item_done();
end

endtask : axi4_read_task

//--------------------------------------------------------------------------------------------
// Task: task_memory_write
// This task is used to write the data into the slave memory
// Parameters:
//  struct_packet   - axi4_write_transfer_char_s
//--------------------------------------------------------------------------------------------

task axi4_slave_driver_proxy::task_memory_write(inout axi4_slave_tx struct_write_packet);
  `uvm_info("DEBUG_MEMORY_WRITE", $sformatf("task_memory_write"), UVM_HIGH); 
  
  for(int j=0;j<struct_write_packet.awlen;j++)begin
    `uvm_info("DEBUG_MEMORY_WRITE",$sformatf("memory_task_awlen=%d",struct_write_packet.awlen),UVM_HIGH)
    if(struct_write_packet.awburst == 2'b00) begin
      for(int i=0; i<(2**(struct_write_packet.awsize)); i++)begin
        `uvm_info("DEBUG_MEMORY_WRITE", $sformatf("task_memory_write inside for loop :: %0d", i), UVM_HIGH);
        `uvm_info("DEBUG_MEMORY_WRITE", $sformatf("task_memory_write inside for loop wstrb = %0h",struct_write_packet.wstrb[i]), UVM_HIGH);
        if(struct_write_packet.wstrb[j][i] == 1)begin
          axi4_slave_agent_cfg_h.slave_memory_task(struct_write_packet.awaddr+i,struct_write_packet.wdata[j][8*i+7 -: 8]);
          `uvm_info("DEBUG_MEMORY_WRITE", $sformatf("task_memory_write inside for loop data = %0h",axi4_slave_agent_cfg_h.slave_memory[struct_write_packet.awaddr+i]), UVM_HIGH);
        end
      end
    end
  end

endtask : task_memory_write

`endif
