`ifndef AXI4_SLAVE_DRIVER_BFMNCLUDED_
`define AXI4_SLAVE_DRIVER_BFMNCLUDED_

//--------------------------------------------------------------------------------------------
//Interface : axi4_slave_driver_bfm
//Used as the HDL driver for axi4
//It connects with the HVL driver_proxy for driving the stimulus
//--------------------------------------------------------------------------------------------
import axi4_globals_pkg::*;
interface axi4_slave_driver_bfm(input           aclk    , 
                                input           aresetn ,
                                //Write_address_channel
                                input    [15:0] awid    ,
                                input    [ADDRESS_WIDTH-1:0] awaddr  ,
                                input    [3: 0] awlen   ,
                                input    [2: 0] awsize  ,
                                input    [1: 0] awburst ,
                                input    [1: 0] awlock  ,
                                input    [3: 0] awcache ,
                                input    [2: 0] awprot  ,
                                input           awvalid ,
                                output reg	    awready ,
                                //Write_data_channel
                                input    [DATA_WIDTH-1: 0] wdata     ,
                                input    [(DATA_WIDTH/8)-1: 0] wstrb ,
                                input           wlast   ,
                                input    [3: 0] wuser   ,
                                input           wvalid  ,
                                output reg	    wready  ,
                                //Write Response Channel
                                output reg[15:0]bid     ,
                                output reg[1:0] bresp   ,
                                output reg[3:0] buser   ,
                                output reg      bvalid  ,
                                input		        bready  ,
                                //Read Address Channel
                                input    [15: 0]arid    ,
                                input    [ADDRESS_WIDTH-1: 0] araddr ,
                                input    [7:0] arlen    ,
                                input    [2:0] arsize   ,
                                input    [1:0] arburst  ,
                                input    [1:0] arlock   ,
                                input    [3:0] arcache  ,
                                input    [2:0] arprot   ,
                                input    [3:0] arQOS    ,
                                input    [3:0] arregion ,
                                input    [3:0] aruser   ,
                                input          arvalid  ,
                                output reg     arready  ,
                                //Read Data Channel
                                output reg[15:0]rid     ,
                                output reg[DATA_WIDTH-1: 0] rdata   ,
                                output reg[(DATA_WIDTH/8)-1: 0]rstrb,
                                output reg[1:0] rresp   ,
                                output reg      rlast   ,
                                output reg[3:0] ruser   ,
                                output reg      rvalid  ,
                                input		        rready  
                              ); 
  //-------------------------------------------------------
  // Importing UVM Package 
  //-------------------------------------------------------
  import uvm_pkg::*;
  `include "uvm_macros.svh" 
  //-------------------------------------------------------
  // Importing axi4 Global Package slave package
  //-------------------------------------------------------
  import axi4_slave_pkg::axi4_slave_driver_proxy;

  //--------------------------------------------------------------------------------------------
  // Creating handle for virtual Interface
  //--------------------------------------------------------------------------------------------
 
  //Variable : axi4_slave_driver_proxy_h
  //Creating the handle for proxy driver
  axi4_slave_driver_proxy axi4_slave_drv_proxy_h;
  
  reg[3:0] i = 0;

  initial begin
    `uvm_info("axi4 slave driver bfm",$sformatf("AXI4 SLAVE DRIVER BFM"),UVM_LOW);
  end

  string name = "AXI4_SLAVE_DRIVER_BFM";

//  reg [	15: 0]	mem_wid		  [MEMD];
//  reg [	ADDRESS_WIDTH-1: 0]	mem_waddr	  [MEMD];
//  reg [	7:0]	    mem_wlen	  [256];
//  reg [	2:0]	    mem_wsize	  [MEMD];
//  reg [ 1	: 0]	    mem_wburst  [MEMD];
//  reg [ 1	: 0]	    mem_wlock	  [MEMD];
//  reg [ 3	: 0]	    mem_wcache  [MEMD];
//  reg [ 2	: 0]	    mem_wprot	  [MEMD];
//  reg [ 3	: 0]	    mem_wQOS  	[MEMD];
//  reg [ 3	: 0]	    mem_wregion	[MEMD];
//  reg [ 3	: 0]	    mem_wuser	  [MEMD];
//
//  reg [	15: 0]	mem_rid		  [MEMD];
//  reg [	ADDRESS_WIDTH-1: 0]	mem_raddr	  [MEMD];
//  reg [	7	: 0]	    mem_rlen	  [256];
//  reg [	2	: 0]	    mem_rsize	  [MEMD];
//  reg [ 1	: 0]	    mem_rburst  [MEMD];
//  reg [ 1	: 0]	    mem_rlock	  [MEMD];
//  reg [ 3	: 0]	    mem_rcache  [MEMD];
//  reg [ 2	: 0]	    mem_rprot	  [MEMD];
//  reg [ 3	: 0]	    mem_rQOS   	[MEMD];
//  reg [ 3	: 0]	    mem_rregion [MEMD];
//  reg [ 3	: 0]	    mem_ruser	  [MEMD];
//
//  task wait_for_system_reset();
//    @(posedge aclk);
//    if(!aresetn) begin
//      `uvmnfo(name,$sformatf("SYSTEM RESET ACTIVATED"),UVM_NONE)
//    end
//    else begin
//      `uvmnfo(name,$sformatf("SYSTEM RESET DI-ACTIVATED"),UVM_NONE)
//    end
//  endtask 
//  
//  
//  task .write_address_phase();
//    
//    @(posedge aclk)begin
//      if(!aresetn)begin
//      end
//      else begin
//        if(.awvalid)begin
//          mem_wid 	[i]	  <= .awid  	;	
//			    mem_waddr	[i] 	<= .awaddr	;	
//			    mem_wlen 	[i]	  <= .awlen	;	
//			    mem_wsize	[i] 	<= .awsize	;	
//			    mem_wburst[i] 	<= .awburst;	
//			    mem_wlock	[i] 	<= .awlock	;	
//			    mem_wcache[i] 	<= .awcache;	
//			    mem_wprot	[i] 	<= .awprot	;	
//			    i <= i+1;
//        end
//      end
//    end
//    assign .awready = .awvalid;
//  endtask
//
//  task write_data_phase();
//
//    @(posedge aclk);
//
//    
//  endtask
    

    








endinterface : axi4_slave_driver_bfm
`endif
