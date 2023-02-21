module wr_addr_phase#(
parameter           AXI_DW         =  64           ,
parameter           AXI_AW         =  32           ,
parameter           AXI_IW         =   4           ,
parameter           AXI_SW         = AXI_DW >> 3 
)
(
   input                     axi_clk_i      ,
   input                     axi_rstn_i     ,
   input      [ AXI_IW-1: 0] axi_awid_i     ,
   input      [ AXI_AW-1: 0] axi_awaddr_i   ,
   input      [      4-1: 0] axi_awlen_i    ,
   input      [      3-1: 0] axi_awsize_i   ,
   input      [      2-1: 0] axi_awburst_i  ,
   input      [      2-1: 0] axi_awlock_i   ,
   input      [      4-1: 0] axi_awcache_i  ,
   input      [      3-1: 0] axi_awprot_i   ,
   input      [      4-1: 0] axi_awQOS_i    , 
   input      [      4-1: 0] axi_awregion_i ,
   input      [      4-1: 0] axi_awuser_i   ,   
   input                     axi_awvalid_i  ,
   
   input		     axi_awready_o  
);

 
always@(posedge axi_clk_i)begin
	if(!axi_rstn_i)begin
	end
	else begin
		if(axi_awvalid_i && axi_awready_o)begin
			mem_top.mem_wid 	[mem_top.addr_wlast_cnt]	= axi_awid_i	;	
			mem_top.mem_waddr	[mem_top.addr_wlast_cnt] = axi_awaddr_i	;	
			mem_top.mem_wlen 	[mem_top.addr_wlast_cnt]	= axi_awlen_i	;	
			mem_top.mem_wsize	[mem_top.addr_wlast_cnt]	= axi_awsize_i	;	
			mem_top.mem_wburst[mem_top.addr_wlast_cnt] = axi_awburst_i;	
			mem_top.mem_wlock	[mem_top.addr_wlast_cnt]	= axi_awlock_i	;	
			mem_top.mem_wcache[mem_top.addr_wlast_cnt]	= axi_awcache_i;	
			mem_top.mem_wprot	[mem_top.addr_wlast_cnt] = axi_awprot_i	;	
			mem_top.addr_wlast_cnt = mem_top.addr_wlast_cnt+1;
		end
	end
end
endmodule

