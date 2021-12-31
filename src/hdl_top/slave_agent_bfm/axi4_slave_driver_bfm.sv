`ifndef AXI4_SLAVE_DRIVER_BFM_INCLUDED_
`define AXI4_SLAVE_DRIVER_BFM_INCLUDED_

//--------------------------------------------------------------------------------------------
//Interface : axi4_slave_driver_bfm
//Used as the HDL driver for axi4
//It connects with the HVL driver_proxy for driving the stimulus
//--------------------------------------------------------------------------------------------
import axi4_globals_pkg::*;
interface axi4_slave_driver_bfm(input                         pclk          , 
                                input                         aresetn       ,
                                input                         aclk          ,
                                //Write_address_channel
                                input           [AXI_IW-1: 0] axi_awid_i    ,
                                input           [AXI_AW-1: 0] axi_awaddr_i  ,
                                input                [4-1: 0] axi_awlen_i   ,
                                input                [3-1: 0] axi_awsize_i  ,
                                input                [2-1: 0] axi_awburst_i ,
                                input                [2-1: 0] axi_awlock_i  ,
                                input                [4-1: 0] axi_awcache_i ,
                                input                [3-1: 0] axi_awprot_i  ,
                                input                         axi_awvalid_i ,
                                output reg		                axi_awready_o ,
                                //Write_data_channel
                                input           [AXI_IW-1: 0] axi_wid_i     ,
                                input           [AXI_DW-1: 0] axi_wdata_i   ,
                                input           [AXI_SW-1: 0] axi_wstrb_i   ,
                                input                         axi_wlast_i   ,
                                input                [4-1: 0] axi_wuser_i   ,
                                input                         axi_wvalid_i  ,
                                output reg	  	              axi_wready_o  ,
                                //Write Response Channel
                                output reg      [AXI_IW-1: 0] axi_bid_o     ,
                                output reg           [2-1: 0] axi_bresp_o   ,
                                output reg           [4-1: 0] axi_buser_o   ,
                                output reg                    axi_bvalid_o  ,
                                input		                      axi_bready_i  ,
                                //Read Address Channel
                                input           [AXI_IW-1: 0] axi_arid_i    ,
                                input           [AXI_AW-1: 0] axi_araddr_i  ,
                                input                [8-1: 0] axi_arlen_i   ,
                                input                [3-1: 0] axi_arsize_i  ,
                                input                [2-1: 0] axi_arburst_i ,
                                input                [2-1: 0] axi_arlock_i  ,
                                input                [4-1: 0] axi_arcache_i ,
                                input                [3-1: 0] axi_arprot_i  ,
                                input                [4-1: 0] axi_arQOS_i   ,
                                input                [4-1: 0] axi_arregion_i,
                                input                [4-1: 0] axi_aruser_i  ,
                                input                         axi_arvalid_i ,
                                output reg		                axi_arready_o ,
                                //Read Data Channel
                                output reg      [AXI_IW-1: 0] axi_rid_o     ,
                                output reg      [AXI_DW-1: 0] axi_rdata_o   ,
                                output reg      [AXI_SW-1: 0] axi_rstrb_o   ,
                                output reg           [2-1: 0] axi_rresp_o   ,
                                output reg                    axi_rlast_o   ,
                                output reg           [4-1: 0] axi_ruser_o   ,
                                output reg                    axi_rvalid_o  ,
                                input		     	                axi_rready_i  
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

  reg [	AXI_IW-1: 0]	mem_wid		  [MEM_ID];
  reg [	AXI_AW-1: 0]	mem_waddr	  [MEM_ID];
  reg [	8-1	: 0]	    mem_wlen	  [256];
  reg [	3-1	: 0]	    mem_wsize	  [MEM_ID];
  reg [ 2-1	: 0]	    mem_wburst  [MEM_ID];
  reg [ 2-1	: 0]	    mem_wlock	  [MEM_ID];
  reg [ 4-1	: 0]	    mem_wcache  [MEM_ID];
  reg [ 3-1	: 0]	    mem_wprot	  [MEM_ID];
  reg [ 4-1	: 0]	    mem_wQOS  	[MEM_ID];
  reg [ 4-1	: 0]	    mem_wregion	[MEM_ID];
  reg [ 4-1	: 0]	    mem_wuser	  [MEM_ID];

  reg [	AXI_IW-1: 0]	mem_rid		  [MEM_ID];
  reg [	AXI_AW-1: 0]	mem_raddr	  [MEM_ID];
  reg [	8-1	: 0]	    mem_rlen	  [256];
  reg [	3-1	: 0]	    mem_rsize	  [MEM_ID];
  reg [ 2-1	: 0]	    mem_rburst  [MEM_ID];
  reg [ 2-1	: 0]	    mem_rlock	  [MEM_ID];
  reg [ 4-1	: 0]	    mem_rcache  [MEM_ID];
  reg [ 3-1	: 0]	    mem_rprot	  [MEM_ID];
  reg [ 4-1	: 0]	    mem_rQOS   	[MEM_ID];
  reg [ 4-1	: 0]	    mem_rregion [MEM_ID];
  reg [ 4-1	: 0]	    mem_ruser	  [MEM_ID];

  task wait_for_system_reset();
    @(posedge aclk);
    if(!aresetn) begin
      `uvm_info(name,$sformatf("SYSTEM RESET ACTIVATED"),UVM_NONE)
    end
    else begin
      `uvm_info(name,$sformatf("SYSTEM RESET DI-ACTIVATED"),UVM_NONE)
    end
  endtask 
  
  
  task axi_write_address_phase();
    
    @(posedge aclk)begin
      if(!aresetn)begin
      end
      else begin
        if(axi_awvalid_i)begin
          mem_wid 	[i]	  <= axi_awid_i  	;	
			    mem_waddr	[i] 	<= axi_awaddr_i	;	
			    mem_wlen 	[i]	  <= axi_awlen_i	;	
			    mem_wsize	[i] 	<= axi_awsize_i	;	
			    mem_wburst[i] 	<= axi_awburst_i;	
			    mem_wlock	[i] 	<= axi_awlock_i	;	
			    mem_wcache[i] 	<= axi_awcache_i;	
			    mem_wprot	[i] 	<= axi_awprot_i	;	
			    i <= i+1;
        end
      end
    end
    assign axi_awready_o = axi_awvalid_i;
  endtask

  task axi_write_data_phase();

    @(posedge aclk);

    
  endtask
    

    








endinterface : axi4_slave_driver_bfm
`endif
