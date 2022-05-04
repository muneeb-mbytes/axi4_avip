
import axi4_globals_pkg::*;

module wr_Addr_phase#(
parameter           AXI_DW         =  DATA_WIDTH   ,
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
   input                     axi_awvalid_i  ,
   output reg		     axi_awready_o  
);

reg[3:0] i = 0;

always@(posedge axi_clk_i)begin
	if(!axi_rstn_i)begin
	end
	else begin
		if(axi_awvalid_i)begin
			axi_top_slave.mem_wid 	[i]	<= axi_awid_i	;	
			axi_top_slave.mem_waddr	[i] 	<= axi_awaddr_i	;	
			axi_top_slave.mem_wlen 	[i]	<= axi_awlen_i	;	
			axi_top_slave.mem_wsize	[i] 	<= axi_awsize_i	;	
			axi_top_slave.mem_wburst[i] 	<= axi_awburst_i;	
			axi_top_slave.mem_wlock	[i] 	<= axi_awlock_i	;	
			axi_top_slave.mem_wcache[i] 	<= axi_awcache_i;	
			axi_top_slave.mem_wprot	[i] 	<= axi_awprot_i	;	
			i <= i+1;
		end
	end
end
assign axi_awready_o = axi_awvalid_i;
endmodule

