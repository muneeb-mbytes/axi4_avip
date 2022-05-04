//`include "wr_addr_phase.sv"
//`include "wr_data_phase.sv"
//`include "wr_resp_phase.sv"
//`include "rd_addr_phase.sv"
//`include "rd_data_phase.sv"

import uvm_pkg::*;
`include "uvm_macros.svh" 

module axi_top_slave 
#(
parameter           AXI_DW         =  32           ,
parameter           AXI_AW         =  32           ,
parameter           AXI_IW         =   4           , 
parameter           MEM_ID         =   2**AXI_IW   , 
parameter           AXI_SW         = AXI_DW >> 3   ,
parameter	          AXI_SI	       =   5
)
(
   input                     axi_clk_i      ,  
   input                     axi_rstn_i     ,  

   input      [ AXI_IW-1: 0] axi_awid_i     , 
   input      [ AXI_AW-1: 0] axi_awaddr_i   , 
   input      [      8-1: 0] axi_awlen_i    , 
   input      [      3-1: 0] axi_awsize_i   ,  
   input      [      2-1: 0] axi_awburst_i  ,  
   input      [      2-1: 0] axi_awlock_i   ,  
   input      [      4-1: 0] axi_awcache_i  ,  
   input      [      3-1: 0] axi_awprot_i   , 
   input      [      4-1: 0] axi_awQOS_i    , 
   input      [      4-1: 0] axi_awregion_i ,
   input      [      4-1: 0] axi_awuser_i   ,
   input                     axi_awvalid_i  ,  
   output                    axi_awready_o  ,  

   input      [ AXI_IW-1: 0] axi_wid_i      ,  
   input      [ AXI_DW-1: 0] axi_wdata_i    ,  
   input      [ AXI_SW-1: 0] axi_wstrb_i    ,  
   input                     axi_wlast_i    ,
   input      [      4-1: 0] axi_wuser_i    ,  
   input                     axi_wvalid_i   ,  
   output                    axi_wready_o   ,  

   output     [ AXI_IW-1: 0] axi_bid_o      ,  
   output reg [      2-1: 0] axi_bresp_o    , 
   output reg [      4-1: 0] axi_buser_o    , 
   output reg                axi_bvalid_o   ,  
   input                     axi_bready_i   ,  

   input      [ AXI_IW-1: 0] axi_arid_i     ,  
   input      [ AXI_AW-1: 0] axi_araddr_i   ,  
   input      [      8-1: 0] axi_arlen_i    ,  
   input      [      3-1: 0] axi_arsize_i   ,  
   input      [      2-1: 0] axi_arburst_i  ,  
   input      [      2-1: 0] axi_arlock_i   ,  
   input      [      4-1: 0] axi_arcache_i  ,  
   input      [      3-1: 0] axi_arprot_i   ,
   input      [      4-1: 0] axi_arQOS_i    ,
   input      [      4-1: 0] axi_arregion_i ,
   input      [      4-1: 0] axi_aruser_i   ,  
   input                     axi_arvalid_i  ,  
   output                    axi_arready_o  ,

   output     [ AXI_IW-1: 0] axi_rid_o      ,  
   output reg [ AXI_DW-1: 0] axi_rdata_o    ,  
   output reg [      2-1: 0] axi_rresp_o    , 
   output reg [ AXI_SW-1: 0] axi_rstrb_o    , 
   output reg                axi_rlast_o    ,
   output reg [      4-1: 0] axi_ruser_o    ,  
   output reg                axi_rvalid_o   ,  
   input                     axi_rready_i   ,

   input                     sys_clk_i      ,  
   output reg [ AXI_AW-1: 0] sys_addr_o     ,  
   output reg [ 8-1: 0]      sys_wdata_o    ,  
   output reg [ AXI_SW-1: 0] sys_sel_o      ,  
   output reg                sys_wen_o      ,  
   output reg                sys_ren_o      ,  
   input      [ 8-1: 0]      sys_rdata_i    ,  
   input                     sys_err_i      ,  
   input                     sys_ack_i         
);


reg [	AXI_IW-1: 0]	mem_wid		[MEM_ID];
reg [	AXI_AW-1: 0]	mem_waddr	[MEM_ID];
reg [	8-1	: 0]	mem_wlen	[256];
reg [	3-1	: 0]	mem_wsize	[MEM_ID];
reg [ 	2-1	: 0]	mem_wburst	[MEM_ID];
reg [ 	2-1	: 0]	mem_wlock	[MEM_ID];
reg [ 	4-1	: 0]	mem_wcache	[MEM_ID];
reg [ 	3-1	: 0]	mem_wprot	[MEM_ID];
reg [ 	4-1	: 0]	mem_wQOS	[MEM_ID];
reg [ 	4-1	: 0]	mem_wregion	[MEM_ID];
reg [ 	4-1	: 0]	mem_wuser	[MEM_ID];

reg [	AXI_IW-1: 0]	mem_rid		[MEM_ID];
reg [	AXI_AW-1: 0]	mem_raddr	[MEM_ID];
reg [	8-1	: 0]	mem_rlen	[256];
reg [	3-1	: 0]	mem_rsize	[MEM_ID];
reg [ 	2-1	: 0]	mem_rburst	[MEM_ID];
reg [ 	2-1	: 0]	mem_rlock	[MEM_ID];
reg [ 	4-1	: 0]	mem_rcache	[MEM_ID];
reg [ 	3-1	: 0]	mem_rprot	[MEM_ID];
reg [ 	4-1	: 0]	mem_rQOS	[MEM_ID];
reg [ 	4-1	: 0]	mem_rregion	[MEM_ID];
reg [ 	4-1	: 0]	mem_ruser	[MEM_ID];

wr_Addr_phase#(AXI_DW,AXI_AW,AXI_IW,AXI_SW,AXI_SI) aw(
		.axi_clk_i	(	axi_clk_i	)	,
		.axi_rstn_i	(	axi_rstn_i	)	,
		.axi_awid_i	(	axi_awid_i	)	, 
    		.axi_awaddr_i	(	axi_awaddr_i	)	, 
    		.axi_awlen_i	(	axi_awlen_i	)	, 
    		.axi_awsize_i	(	axi_awsize_i	)   	,  
    		.axi_awburst_i	(	axi_awburst_i	)   	,  
   		.axi_awlock_i	(	axi_awlock_i	)   	,  
    		.axi_awcache_i	(	axi_awcache_i	)  	,  
    		.axi_awprot_i	(	axi_awprot_i	)   	,
    		.axi_awQOS_i	(	axi_awQOS_i	)   	,
    		.axi_awregion_i	(	axi_awregion_i	)   	, 
    		.axi_awuser_i	(	axi_awuser_i	)   	,
    		.axi_awvalid_i	(	axi_awvalid_i	)  	,  
    		.axi_awready_o	(	axi_awready_o	)  	  
);

wr_data_phase#(AXI_DW,AXI_AW,AXI_IW,AXI_SW,AXI_SI) w(
		.axi_clk_i	(	axi_clk_i	)      	,  
		.axi_rstn_i	(	axi_rstn_i	)     	,	  
		.axi_wid_i	(	axi_wid_i	)      	,  
		.axi_wdata_i	(	axi_wdata_i	)    	,  
		.axi_wstrb_i	(	axi_wstrb_i	)    	,  
		.axi_wlast_i	(	axi_wlast_i	)    	,
    		.axi_wuser_i	(	axi_wuser_i	)   	,  
		.axi_wvalid_i	(	axi_wvalid_i	)   	,  
		.axi_wready_o	(	axi_wready_o	)   	 
		
);


wr_resp_phase#(AXI_DW,AXI_AW,AXI_IW,AXI_SW,AXI_SI) b(
		.axi_clk_i	(	axi_clk_i	)      	,  
		.axi_rstn_i	(	axi_rstn_i	)     	,	  
		.axi_bid_o	(	axi_bid_o	)      	,  
		.axi_bresp_o	(	axi_bresp_o	)    	,
    		.axi_buser_o	(	axi_buser_o	)   	, 
		.axi_bvalid_o	(	axi_bvalid_o	)   	,  
		.axi_bready_i	(	axi_bready_i	)   	 
		
);

rd_Addr_phase#(AXI_DW,AXI_AW,AXI_IW,AXI_SW,AXI_SI) ar(
		.axi_clk_i	(	axi_clk_i	)	,
		.axi_rstn_i	(	axi_rstn_i	)	,
		.axi_arid_i	(	axi_arid_i	)	, 
    		.axi_araddr_i	(	axi_araddr_i	)	, 
    		.axi_arlen_i	(	axi_arlen_i	)	, 
    		.axi_arsize_i	(	axi_arsize_i	)   	,  
    		.axi_arburst_i	(	axi_arburst_i	)   	,  
   		.axi_arlock_i	(	axi_arlock_i	)   	,  
    		.axi_arcache_i	(	axi_arcache_i	)  	,  
    		.axi_arprot_i	(	axi_arprot_i	)   	, 
    		.axi_arQOS_i	(	axi_arQOS_i	)   	,
    		.axi_arregion_i	(	axi_arregion_i	)   	,
    		.axi_aruser_i	(	axi_aruser_i	)   	,  
    		.axi_arvalid_i	(	axi_arvalid_i	)  	,  
    		.axi_arready_o	(	axi_arready_o	)  	  
);

rd_data_phase#(AXI_DW,AXI_AW,AXI_IW,AXI_SW,AXI_SI) r(
		.axi_clk_i	(	axi_clk_i	)      	,  
		.axi_rstn_i	(	axi_rstn_i	)     	,	  
		.axi_rid_o	(	axi_rid_o	)      	,  
		.axi_rdata_o	(	axi_rdata_o	)    	, 
                .axi_rresp_o    (       axi_rresp_o     )       , 
		.axi_rstrb_o	(	axi_rstrb_o	)    	,  
		.axi_rlast_o	(	axi_rlast_o	)    	,
    		.axi_ruser_o	(	axi_ruser_o	)   	,   
		.axi_rvalid_o	(	axi_rvalid_o	)   	,  
		.axi_rready_i	(	axi_rready_i	)   	 
		
);

endmodule


