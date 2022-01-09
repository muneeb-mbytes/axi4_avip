`ifndef AXI4_MASTER_DRIVER_BFM_INCLUDED_
`define AXI4_MASTER_DRIVER_BFM_INCLUDED_

//Importing global package
import axi4_globals_pkg::*;

//--------------------------------------------------------------------------------------------
// Interface : axi4_master_driver_bfm
//  Used as the HDL driver for axi4
//  It connects with the HVL driver_proxy for driving the stimulus
//--------------------------------------------------------------------------------------------
interface axi4_master_driver_bfm(input                    aclk    , 
                                 input                    aresetn ,
                                 
                                 //Write_address_channel
                                 input [3:0]              awid    ,
                                 input [ADDRESS_WIDTH-1:0]awaddr  ,
                                 input [3: 0]             awlen   ,
                                 input [2: 0]             awsize  ,
                                 input [1: 0]             awburst ,
                                 input [1: 0]             awlock  ,
                                 input [3: 0]             awcache ,
                                 input [2: 0]             awprot  ,
                                 input                    awvalid ,
                                 output reg	              awready ,

                                 //Write_data_channel
                                 input [DATA_WIDTH-1: 0]    wdata  ,
                                 input [(DATA_WIDTH/8)-1: 0]wstrb  ,
                                 input                      wlast  ,
                                 input [3: 0]               wuser  ,
                                 input                      wvalid ,
                                 output reg	                wready ,

                                 //Write Response Channel
                                 output reg [3:0]bid    ,
                                 output reg [1:0]bresp  ,
                                 output reg [3:0]buser  ,
                                 output reg bvalid ,
                                 input		  bready ,

                                 //Read Address Channel
                                 input [3: 0]              arid    ,
                                 input [ADDRESS_WIDTH-1: 0]araddr  ,
                                 input [7:0]               arlen   ,
                                 input [2:0]               arsize  ,
                                 input [1:0]               arburst ,
                                 input [1:0]               arlock  ,
                                 input [3:0]               arcache ,
                                 input [2:0]               arprot  ,
                                 input [3:0]               arQOS   ,
                                 input [3:0]               arregion,
                                 input [3:0]               aruser  ,
                                 input                     arvalid ,
                                 output reg                arready ,

                                 //Read Data Channel
                                 output reg [3:0]                rid     ,
                                 output reg [DATA_WIDTH-1: 0]    rdata   ,
                                 output reg [(DATA_WIDTH/8)-1: 0]rstrb   ,
                                 output reg [1:0]                rresp   ,
                                 output reg                      rlast   ,
                                 output reg [3:0]                ruser   ,
                                 output reg                      rvalid  ,
                                 input		                       rready  
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
    `uvm_info(name,$sformatf("AXI4 MASTER DRIVER BFM"),UVM_LOW);
  end

  //-------------------------------------------------------
  // Task: wait_for_areset_n
  // Waiting for the system reset to be active low
  //-------------------------------------------------------
  task wait_for_areset_n();
    @(negedge aresetn);
    `uvm_info(name ,$sformatf("SYSTEM RESET DETECTED"),UVM_HIGH)
 
    @(posedge aresetn);
    `uvm_info(name ,$sformatf("SYSTEM RESET DEACTIVATED"),UVM_HIGH)
  endtask: wait_for_areset_n

  //-------------------------------------------------------
  // Task: axi4_write_address_channel_task
  // This task will drive the write address signals
  //-------------------------------------------------------
  task axi4_write_address_channel_task (inout axi4_write_transfer_char_s data_write_packet, input axi4_transfer_cfg_s cfg_packet);
    `uvm_info(name,$sformatf("data_write_packet=\n%p",data_write_packet),UVM_HIGH);
    `uvm_info(name,$sformatf("cfg_packet=\n%p",cfg_packet),UVM_HIGH);
    `uvm_info(name,$sformatf("DRIVE TO WRITE ADDRESS CHANNEL"),UVM_HIGH);
  endtask : axi4_write_address_channel_task

  //-------------------------------------------------------
  // Task: axi4_write_data_channel_task
  // This task will drive the write data signals
  //-------------------------------------------------------
  task axi4_write_data_channel_task (inout axi4_write_transfer_char_s data_write_packet, input axi4_transfer_cfg_s cfg_packet);
    `uvm_info(name,$sformatf("data_write_packet=\n%p",data_write_packet),UVM_HIGH);
    `uvm_info(name,$sformatf("cfg_packet=\n%p",cfg_packet),UVM_HIGH);
    `uvm_info(name,$sformatf("DRIVE TO WRITE DATA CHANNEL"),UVM_HIGH);
  endtask : axi4_write_data_channel_task

  //-------------------------------------------------------
  // Task: axi4_write_response_channel_task
  // This task will drive the write response signals
  //-------------------------------------------------------
  task axi4_write_response_channel_task (inout axi4_write_transfer_char_s data_write_packet, input axi4_transfer_cfg_s cfg_packet);
    `uvm_info(name,$sformatf("data_write_packet=\n%p",data_write_packet),UVM_HIGH);
    `uvm_info(name,$sformatf("cfg_packet=\n%p",cfg_packet),UVM_HIGH);
    `uvm_info(name,$sformatf("DRIVE TO WRITE RESPONSE CHANNEL"),UVM_HIGH);
  endtask : axi4_write_response_channel_task

  //-------------------------------------------------------
  // Task: axi4_read_address_channel_task
  // This task will drive the read address signals
  //-------------------------------------------------------
  task axi4_read_address_channel_task (inout axi4_read_transfer_char_s data_read_packet, input axi4_transfer_cfg_s cfg_packet);
    `uvm_info(name,$sformatf("data_read_packet=\n%p",data_read_packet),UVM_HIGH);
    `uvm_info(name,$sformatf("cfg_packet=\n%p",cfg_packet),UVM_HIGH);
    `uvm_info(name,$sformatf("DRIVE TO READ ADDRESS CHANNEL"),UVM_HIGH);
  endtask : axi4_read_address_channel_task

  //-------------------------------------------------------
  // Task: axi4_read_data_channel_task
  // This task will drive the read data signals
  //-------------------------------------------------------
  task axi4_read_data_channel_task (inout axi4_read_transfer_char_s data_read_packet, input axi4_transfer_cfg_s cfg_packet);
    `uvm_info(name,$sformatf("data_read_packet=\n%p",data_read_packet),UVM_HIGH);
    `uvm_info(name,$sformatf("cfg_packet=\n%p",cfg_packet),UVM_HIGH);
    `uvm_info(name,$sformatf("DRIVE TO READ DATA CHANNEL"),UVM_HIGH);
  endtask : axi4_read_data_channel_task

endinterface : axi4_master_driver_bfm

`endif

