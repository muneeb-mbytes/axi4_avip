`include "wr_addr_phase.sv"
`include "wr_data_phase.sv"
//`include "wr_resp_phase.sv"
`include "rd_addr_phase.sv"
`include "rd_data_phase.sv"
module mem_top
#(
parameter           AXI_DW         =  32           ,
parameter           AXI_AW         =  32           ,
parameter           AXI_IW         =   4           , 
parameter           MEM_ID         =   2**AXI_IW   , 
parameter           AXI_SW         = AXI_DW >> 3   ,
parameter	    AXI_SI	   =   5
)(axi4_if intf,axi_slave_intf pif1,input axi_clk_i,sys_clk_i,input axi_rstn_i);

   wire    [ AXI_IW-1: 0] axi_awid_i     ; 
   wire    [ AXI_AW-1: 0] axi_awaddr_i   ; 
   wire    [      8-1: 0] axi_awlen_i    ; 
   wire    [      3-1: 0] axi_awsize_i   ;  
   wire    [      2-1: 0] axi_awburst_i  ;  
   wire    [      2-1: 0] axi_awlock_i   ;  
   wire    [      4-1: 0] axi_awcache_i  ;  
   wire    [      3-1: 0] axi_awprot_i   ; 
   wire    [      4-1: 0] axi_awQOS_i    ; 
   wire    [      4-1: 0] axi_awregion_i ;
   wire    [      4-1: 0] axi_awuser_i   ;
   wire                   axi_awvalid_i  ;  
   wire                   axi_awready_o  ;  

   wire    [ AXI_DW-1: 0] axi_wdata_i    ;  
   wire    [ AXI_SW-1: 0] axi_wstrb_i    ;  
   wire                   axi_wlast_i    ;
   wire    [      4-1: 0] axi_wuser_i    ;  
   wire                   axi_wvalid_i   ;  
   wire                   axi_wready_o   ;  

   wire    [ AXI_IW-1: 0] axi_arid_i     ;  
   wire    [ AXI_AW-1: 0] axi_araddr_i   ;  
   wire    [      8-1: 0] axi_arlen_i    ;  
   wire    [      3-1: 0] axi_arsize_i   ;  
   wire    [      2-1: 0] axi_arburst_i  ;  
   wire    [      2-1: 0] axi_arlock_i   ;  
   wire    [      4-1: 0] axi_arcache_i  ;  
   wire    [      3-1: 0] axi_arprot_i   ;
   wire    [      4-1: 0] axi_arQOS_i    ;
   wire    [      4-1: 0] axi_arregion_i ;
   wire    [      4-1: 0] axi_aruser_i   ;  
   wire                   axi_arvalid_i  ;  
   wire                   axi_arready_o  ;

   wire [ AXI_IW-1: 0] axi_rid_o      ;  
   wire [ AXI_DW-1: 0] axi_rdata_o    ;  
   wire [      2-1: 0] axi_rresp_o    ; 
   wire [ AXI_SW-1: 0] axi_rstrb_o    ; 
   wire                axi_rlast_o    ;
   wire [      4-1: 0] axi_ruser_o    ;  
   wire                axi_rvalid_o   ;  
   wire                axi_rready_i   ;

   reg [ AXI_AW-1: 0] sys_addr_o     ;  
   reg [ 8-1: 0]      sys_wdata_o    ;  
   reg [ AXI_SW-1: 0] sys_sel_o      ;  
   reg                sys_wen_o      ;  
   reg                sys_ren_o      ;  
   reg    [ 8-1: 0]   sys_rdata_i    ;
   int                wlast_cnt      ;
   int                addr_wlast_cnt ;
   bit                read_data_phase_start;


reg  [  AXI_IW-1:  0]             mem_wid      [MEM_ID];
reg  [  AXI_AW-1:  0]             mem_waddr    [MEM_ID];
reg  [  8-1        :   0]         mem_wlen     [256];
reg  [  3-1        :   0]         mem_wsize    [MEM_ID];
reg  [  2-1        :   0]         mem_wburst   [MEM_ID];
reg  [  2-1        :   0]         mem_wlock    [MEM_ID];
reg  [  4-1        :   0]         mem_wcache   [MEM_ID];
reg  [  3-1        :   0]         mem_wprot    [MEM_ID];
reg  [  4-1        :   0]         mem_wQOS     [MEM_ID];
reg  [  4-1        :   0]         mem_wregion  [MEM_ID];
reg  [  4-1        :   0]         mem_wuser    [MEM_ID];
reg  [  AXI_IW-1:  0]             mem_rid      [MEM_ID];
reg  [  AXI_AW-1:  0]             mem_raddr    [MEM_ID];
reg  [  8-1        :   0]         mem_rlen     [256];
reg  [  3-1        :   0]         mem_rsize    [MEM_ID];
reg  [  2-1        :   0]         mem_rburst   [MEM_ID];
reg  [  2-1        :   0]         mem_rlock    [MEM_ID];
reg  [  4-1        :   0]         mem_rcache   [MEM_ID];
reg  [  3-1        :   0]         mem_rprot    [MEM_ID];
reg  [  4-1        :   0]         mem_rQOS     [MEM_ID];
reg  [  4-1        :   0]         mem_rregion  [MEM_ID];
reg  [  4-1        :   0]         mem_ruser    [MEM_ID];


wr_addr_phase#(AXI_DW,AXI_AW,AXI_IW,AXI_SW) aw(
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
		.axi_wdata_i	(	axi_wdata_i	)    	,  
		.axi_wstrb_i	(	axi_wstrb_i	)    	,  
		.axi_wlast_i	(	axi_wlast_i	)    	,
		.axi_wuser_i	(	axi_wuser_i	)   	,  
		.axi_wvalid_i	(	axi_wvalid_i	)   ,	
		.axi_wready_o	(	axi_wready_o	)   	 
		
);


//`wr_resp_phase#(AXI_DW,AXI_AW,AXI_IW,AXI_SW,AXI_SI) b(
//`		.axi_clk_i	(	axi_clk_i	)      	,  
//`		.axi_rstn_i	(	axi_rstn_i	)     	,	  
//`		.axi_bid_o	(	axi_bid_o	)      	,  
//`		.axi_bresp_o	(	axi_bresp_o	)    	,
//`    		.axi_buser_o	(	axi_buser_o	)   	, 
//`		.axi_bvalid_o	(	axi_bvalid_o	)   	,  
//`		.axi_bready_i	(	axi_bready_i	)   	 
//`		
//`);
//`
rd_addr_phase#(AXI_DW,AXI_AW,AXI_IW,AXI_SW,AXI_SI) ar(
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

               
assign  axi_awid_i    =  intf.awid      ;
assign  axi_awaddr_i  =  intf.awaddr    ;
assign  axi_awlen_i   =  intf.awlen     ;
assign  axi_awsize_i  =  intf.awsize    ;
assign  axi_awburst_i =  intf.awburst   ;
assign  axi_awlock_i  =  intf.awlock    ;
assign  axi_awcache_i =  intf.awcache   ;
assign  axi_awprot_i  =  intf.awprot    ;
assign  axi_awQOS_i   =  intf.awqos     ;
assign  axi_awregion_i=  intf.awregion  ;
assign  axi_awuser_i  =  intf.awuser    ;
assign  axi_awvalid_i =  intf.awvalid   ;
assign  axi_awready_o =  intf.awready   ;

assign axi_wdata_i   =  intf.wdata     ;
assign axi_wstrb_i   =  intf.wstrb     ;
assign axi_wlast_i   =  intf.wlast     ;
assign axi_wuser_i   =  intf.wuser     ;
assign axi_wvalid_i  =  intf.wvalid    ;
assign axi_wready_o  =  intf.wready    ;

assign axi_arid_i    =  intf.arid      ;
assign axi_araddr_i  =  intf.araddr    ;
assign axi_arlen_i   =  intf.arlen     ;
assign axi_arsize_i  =  intf.arsize    ;
assign axi_arburst_i =  intf.arburst   ;
assign axi_arlock_i  =  intf.arlock    ;
assign axi_arcache_i =  intf.arcache   ;
assign axi_arprot_i  =  intf.arprot    ;
assign axi_arQOS_i   =  intf.arqos     ;
assign axi_arregion_i = intf.arregion  ;
assign axi_aruser_i  =  intf.aruser    ;
assign axi_arvalid_i =  intf.arvalid   ;
assign axi_arready_o =  intf.arready   ;

assign axi_rready_i = intf.rready     ;

`ifdef AXI_SLAVE_MEM
assign intf.rid = axi_rid_o;
assign intf.rdata = axi_rdata_o;
assign intf.rresp = axi_rresp_o;
assign intf.rlast = axi_rlast_o;
assign intf.ruser = axi_ruser_o;
assign intf.rvalid = axi_rvalid_o;
`endif

assign  pif1.sys_addr_o  =  sys_addr_o  ; 
assign  pif1.sys_wdata_o =  sys_wdata_o ; 
assign  pif1.sys_sel_o   =  sys_sel_o   ; 
assign  pif1.sys_wen_o   =  sys_wen_o   ; 
assign  pif1.sys_ren_o   =  sys_ren_o   ; 
assign  sys_rdata_i      =  pif1.sys_rdata_i;

endmodule


