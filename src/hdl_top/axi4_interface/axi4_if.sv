`ifndef AXI4_IF_INCLUDED_
`define AXI4_IF_INCLUDED_

// Import axi4_globals_pkg 
import axi4_globals_pkg::*;

//--------------------------------------------------------------------------------------------
// Interface : axi4_if
// Declaration of pin level signals for axi4 interface
//--------------------------------------------------------------------------------------------
interface axi4_if(input aclk, input aresetn);

 // // Variable: aclk
 // // axi4 clock signal
 // bit aclk;

  //Write_address_channel
  logic     [AXI_IW-1: 0] axi_awid      ;
  logic     [AXI_AW-1: 0] axi_awaddr    ;
  logic          [4-1: 0] axi_awlen     ;
  logic          [3-1: 0] axi_awsize    ;
  logic          [2-1: 0] axi_awburst   ;
  logic          [2-1: 0] axi_awlock    ;
  logic          [4-1: 0] axi_awcache   ;
  logic          [3-1: 0] axi_awprot    ;
  logic                   axi_awvalid   ;
  logic		                axi_awready   ;
  //Write_data_channel
  logic     [AXI_IW-1: 0] axi_wid       ;
  logic     [AXI_DW-1: 0] axi_wdata     ;
  logic     [AXI_SW-1: 0] axi_wstrb     ;
  logic                   axi_wlast     ;
  logic          [4-1: 0] axi_wuser     ;
  logic                   axi_wvalid    ;
 	logic   	              axi_wready    ;
  //Write Response Channel
  logic      [AXI_IW-1: 0] axi_bid      ;
  logic          [2-1: 0] axi_bresp     ;
  logic          [4-1: 0] axi_buser     ;
  logic                   axi_bvalid    ;
  logic                   axi_bready    ;
  //Read Address Channel
  logic     [AXI_IW-1: 0] axi_arid      ;
  logic     [AXI_AW-1: 0] axi_araddr    ;
  logic          [8-1: 0] axi_arlen     ;
  logic          [3-1: 0] axi_arsize    ;
  logic          [2-1: 0] axi_arburst   ;
  logic          [2-1: 0] axi_arlock    ;
  logic          [4-1: 0] axi_arcache   ;
  logic          [3-1: 0] axi_arprot    ;
  logic          [4-1: 0] axi_arQOS     ;
  logic          [4-1: 0] axi_arregion  ;
  logic          [4-1: 0] axi_aruser    ;
  logic                   axi_arvalid   ;
 	logic	                  axi_arready   ;
  //Read Data Channel
  logic     [AXI_IW-1: 0] axi_rid       ;
  logic     [AXI_DW-1: 0] axi_rdata     ;
  logic     [AXI_SW-1: 0] axi_rstrb     ;
  logic          [2-1: 0] axi_rresp     ;
  logic                   axi_rlast     ;
  logic          [4-1: 0] axi_ruser     ;
  logic                   axi_rvalid    ;
  logic  	                axi_rready    ;
  

endinterface: axi4_if 

`endif
