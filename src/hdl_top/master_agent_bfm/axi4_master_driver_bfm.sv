`ifndef AXI4_MASTER_DRIVER_BFM_INCLUDED_
`define AXI4_MASTER_DRIVER_BFM_INCLUDED_

//-------------------------------------------------------
// Importing global package
//-------------------------------------------------------
import axi4_globals_pkg::*;

//--------------------------------------------------------------------------------------------
// Interface : axi4_master_driver_bfm
//  Used as the HDL driver for axi4
//  It connects with the HVL driver_proxy for driving the stimulus
//--------------------------------------------------------------------------------------------
interface axi4_master_driver_bfm(input bit                aclk    , 
                                 input bit                aresetn ,
                                 
                                 //Write_address_channel
                                 output reg [3:0]              awid    ,
                                 output reg [ADDRESS_WIDTH-1:0]awaddr  ,
                                 output reg  [3:0]              awlen   ,
                                 output reg  [2:0]              awsize  ,
                                 output reg  [1:0]              awburst ,
                                 output reg  [1:0]              awlock  ,
                                 output reg  [3:0]              awcache ,
                                 output reg  [2:0]              awprot  ,
                                 output reg                     awvalid ,
                                 input    	               awready ,

                                 //Write_data_channel
                                 output reg    [DATA_WIDTH-1: 0]wdata  ,
                                 output reg [(DATA_WIDTH/8)-1:0]wstrb  ,
                                 output reg                     wlast  ,
                                 output reg                [3:0]wuser  ,
                                 output reg                     wvalid ,
                                 input                   wready ,

                                 //Write Response Channel
                                 output reg [3:0]bid    ,
                                 output reg [1:0]bresp  ,
                                 output reg [3:0]buser  ,
                                 output reg  bvalid ,
                                 input	 bready ,

                                 //Read Address Channel
                                 output reg [3: 0]              arid    ,
                                 output reg [ADDRESS_WIDTH-1: 0]araddr  ,
                                 output reg [7:0]               arlen   ,
                                 output reg [2:0]               arsize  ,
                                 output reg [1:0]               arburst ,
                                 output reg [1:0]               arlock  ,
                                 output reg [3:0]               arcache ,
                                 output reg [2:0]               arprot  ,
                                 output reg [3:0]               arQOS   ,
                                 output reg [3:0]               arregion,
                                 output reg [3:0]               aruser  ,
                                 output reg                     arvalid ,
                                 input                          arready ,

                                 //Read Data Channel
                                 output reg [3:0]                rid     ,
                                 output reg [DATA_WIDTH-1: 0]    rdata   ,
                                 output reg [1:0]                rresp   ,
                                 output reg                      rlast   ,
                                 output reg [3:0]                ruser   ,
                                 output reg                      rvalid  ,
                                 input	                     rready  
                                );  
  
  //-------------------------------------------------------
  // Importing UVM Package 
  //-------------------------------------------------------
  import uvm_pkg::*;
  `include "uvm_macros.svh" 

  //-------------------------------------------------------
  // Importing axi4 Global Package master package
  //-------------------------------------------------------
  import axi4_master_pkg::axi4_master_driver_proxy;

  //Variable : name
  //Used to store the name of the interface
  string name = "AXI4_MASTER_DRIVER_BFM"; 

  //Variable : axi4_master_driver_proxy_h
  //Creating the handle for master driver proxy
  axi4_master_driver_proxy axi4_master_drv_proxy_h;

  initial begin
    `uvm_info(name,$sformatf(name),UVM_LOW)
  end

  //-------------------------------------------------------
  // Task: wait_for_areset_n
  // Waiting for the system reset to be active low
  //-------------------------------------------------------
  task wait_for_areset_n();
    @(negedge aresetn);
    `uvm_info(name,$sformatf("SYSTEM RESET DETECTED"),UVM_HIGH)
 
    @(posedge aresetn);
    `uvm_info(name,$sformatf("SYSTEM RESET DEACTIVATED"),UVM_HIGH)
  endtask : wait_for_areset_n

  //-------------------------------------------------------
  // Task: detect_write_address_wait_state
  // Waiting for the awready to set to high to setup the address,
  // in write address channel
  //-------------------------------------------------------
  task detect_write_address_wait_state(inout axi4_write_transfer_char_s data_write_packet);
    @(posedge aclk);
    `uvm_info(name,$sformatf("DETECT_WRITE_ADDRESS_WAIT_STATE"),UVM_HIGH)

    while(awready==0) begin
      @(posedge aclk);
      data_write_packet.wait_count_write_address_channel++;
    end
  endtask : detect_write_address_wait_state

  //-------------------------------------------------------
  // Task: detect_write_data_wait_state
  // Waiting for the wready to set to high to transfer the data packet,
  // in write address channel
  //-------------------------------------------------------
  task detect_write_data_wait_state(inout axi4_write_transfer_char_s data_write_packet);
    @(posedge aclk);
    `uvm_info(name,$sformatf("DETECT_WRITE_DATA_WAIT_STATE"),UVM_HIGH)

    while(wready==0) begin
      @(posedge aclk);
      data_write_packet.wait_count_write_data_channel++;
    end
  endtask : detect_write_data_wait_state

  //-------------------------------------------------------
  // Task: detect_write_response_wait_state
  // Waiting for the bready to set to high to get the response,
  // in write response channel
  //-------------------------------------------------------
  task detect_write_response_wait_state(inout axi4_write_transfer_char_s data_write_packet);
    @(posedge aclk);
    `uvm_info(name,$sformatf("DETECT_WRITE_RESPONSE_WAIT_STATE"),UVM_HIGH)

    while(bready==0) begin
      @(posedge aclk);
      data_write_packet.wait_count_write_response_channel++;
    end
  endtask : detect_write_response_wait_state

  //-------------------------------------------------------
  // Task: detect_read_address_wait_state
  // Waiting for the arready to set to high to setup the address,
  // in read address channel
  //-------------------------------------------------------
  task detect_read_address_wait_state(inout axi4_read_transfer_char_s data_read_packet);
    @(posedge aclk);
    `uvm_info(name,$sformatf("DETECT_READ_ADDRESS_WAIT_STATE"),UVM_HIGH)

    while(arready==0) begin
      @(posedge aclk);
      data_read_packet.wait_count_read_address_channel++;
    end
  endtask : detect_read_address_wait_state

  //-------------------------------------------------------
  // Task: detect_read_data_wait_state
  // Waiting for the rready to set to high for data transfer and 
  // to get the response back, in read data channel
  //-------------------------------------------------------
  task detect_read_data_wait_state(inout axi4_read_transfer_char_s data_read_packet);
    @(posedge aclk);
    `uvm_info(name,$sformatf("DETECT_READ_DATA_WAIT_STATE"),UVM_HIGH)

    while(rready==0) begin
      @(posedge aclk);
      data_read_packet.wait_count_read_data_channel++;
    end
  endtask : detect_read_data_wait_state

  //-------------------------------------------------------
  // Task: axi4_write_address_channel_task
  // This task will drive the write address signals
  //-------------------------------------------------------
  task axi4_write_address_channel_task (inout axi4_write_transfer_char_s data_write_packet, axi4_transfer_cfg_s cfg_packet);
    @(posedge aclk);

    `uvm_info(name,$sformatf("data_write_packet=\n%p",data_write_packet),UVM_HIGH)
    `uvm_info(name,$sformatf("cfg_packet=\n%p",cfg_packet),UVM_HIGH)
    `uvm_info(name,$sformatf("DRIVING WRITE ADDRESS CHANNEL"),UVM_HIGH)

      awid    <= data_write_packet.awid;
      awaddr  <= data_write_packet.awaddr;
      awlen   <= data_write_packet.awlen;
      awsize  <= data_write_packet.awsize;
      awburst <= data_write_packet.awburst;
      awlock  <= data_write_packet.awlock;
      awcache <= data_write_packet.awcache;
      awprot  <= data_write_packet.awprot;
      awvalid <= 1'b1;
      
      if (awready==0) begin
        detect_write_address_wait_state(data_write_packet);
      end

   //TODO:SAHA
   //should we add else?
   //else begin
   //  awid    = 1'b0;
   //  awaddr  = 1'b0;
   //  awlen   = 1'b0;
   //  awsize  = 1'b0;
   //  awburst = 1'b0;
   //  awlock  = 1'b0;
   //  awcache = 1'b0;
   //  awprot  = 1'b0;
   //end
  endtask : axi4_write_address_channel_task

  //-------------------------------------------------------
  // Task: axi4_write_data_channel_task
  // This task will drive the write data signals
  //-------------------------------------------------------
  task axi4_write_data_channel_task (inout axi4_write_transfer_char_s data_write_packet, input axi4_transfer_cfg_s cfg_packet);
    `uvm_info(name,$sformatf("data_write_packet=\n%p",data_write_packet),UVM_HIGH)
    `uvm_info(name,$sformatf("cfg_packet=\n%p",cfg_packet),UVM_HIGH)
    `uvm_info(name,$sformatf("DRIVE TO WRITE DATA CHANNEL"),UVM_HIGH)

      wdata  <= data_write_packet.wdata;
      wstrb  <= data_write_packet.wstrb; 
      wlast  <= data_write_packet.wlast;
      wuser  <= data_write_packet.wuser;
      wvalid <= 1'b1;
      
      if(wready==0) begin
        detect_write_data_wait_state(data_write_packet);
      end

    //TODO:SAHA
    //write else also
  endtask : axi4_write_data_channel_task

  //-------------------------------------------------------
  // Task: axi4_write_response_channel_task
  // This task will drive the write response signals
  //-------------------------------------------------------
  task axi4_write_response_channel_task (inout axi4_write_transfer_char_s data_write_packet, input axi4_transfer_cfg_s cfg_packet);
    `uvm_info(name,$sformatf("data_write_packet=\n%p",data_write_packet),UVM_HIGH)
    `uvm_info(name,$sformatf("cfg_packet=\n%p",cfg_packet),UVM_HIGH)
    `uvm_info(name,$sformatf("DRIVE TO WRITE RESPONSE CHANNEL"),UVM_HIGH)

    bid    <= data_write_packet.bid;
    bresp  <= data_write_packet.bresp;
    //buser  <= data_write_packet.buser;
    bvalid <= 1'b1;

    if(bready==0) begin
      detect_write_response_wait_state(data_write_packet);
    end

    //TODO:SAHA
    //else
  endtask : axi4_write_response_channel_task

  //-------------------------------------------------------
  // Task: axi4_read_address_channel_task
  // This task will drive the read address signals
  //-------------------------------------------------------
  task axi4_read_address_channel_task (inout axi4_read_transfer_char_s data_read_packet, input axi4_transfer_cfg_s cfg_packet);
    `uvm_info(name,$sformatf("data_read_packet=\n%p",data_read_packet),UVM_HIGH)
    `uvm_info(name,$sformatf("cfg_packet=\n%p",cfg_packet),UVM_HIGH)
    `uvm_info(name,$sformatf("DRIVE TO READ ADDRESS CHANNEL"),UVM_HIGH)

    arid    <= data_read_packet.arid;
    araddr  <= data_read_packet.araddr;
    arlen   <= data_read_packet.arlen;
    arsize  <= data_read_packet.arsize;
    arburst <= data_read_packet.arburst;
    arlock  <= data_read_packet.arlock;
    arcache <= data_read_packet.arcache;
    arprot  <= data_read_packet.arprot;
    arvalid <= 1'b1;
    
    if (arready==0) begin
      detect_read_address_wait_state(data_read_packet);
    end

   //TODO:SAHA
   //else
  endtask : axi4_read_address_channel_task

  //-------------------------------------------------------
  // Task: axi4_read_data_channel_task
  // This task will drive the read data signals
  //-------------------------------------------------------
  task axi4_read_data_channel_task (inout axi4_read_transfer_char_s data_read_packet, input axi4_transfer_cfg_s cfg_packet);
    `uvm_info(name,$sformatf("data_read_packet=\n%p",data_read_packet),UVM_HIGH)
    `uvm_info(name,$sformatf("cfg_packet=\n%p",cfg_packet),UVM_HIGH)
    `uvm_info(name,$sformatf("DRIVE TO READ DATA CHANNEL"),UVM_HIGH)

   rid    <= data_read_packet.rid;
   rdata  <= data_read_packet.rdata;
   rresp  <= data_read_packet.rresp;
 //  rlast  <= data_read_packet.rlast;
 //  ruser  <= data_read_packet.ruser;
   rvalid <= 1'b1;
   
   if(rready==0) begin
     detect_read_data_wait_state(data_read_packet);
   end;

   //TODO:SAHA
   //else
  endtask : axi4_read_data_channel_task

endinterface : axi4_master_driver_bfm

`endif

