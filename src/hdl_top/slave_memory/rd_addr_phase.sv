module rd_addr_phase#(
parameter           AXI_DW         =  256          ,
parameter           AXI_AW         =  32           ,
parameter           AXI_IW         =   4           ,
parameter           AXI_SW         = AXI_DW >> 3   ,
parameter	    AXI_SI	   =   5
)
(
   input                     axi_clk_i      ,
   input                     axi_rstn_i     ,
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
   input            		     axi_arready_o  
);

reg[15:0] i = 0;

always@(posedge axi_clk_i)begin
	if(!axi_rstn_i)begin
	end
	else begin
		if(axi_arvalid_i && axi_arready_o)begin
			mem_top.mem_rid 	[i]	= axi_arid_i	;	
			mem_top.mem_raddr	[i] 	= axi_araddr_i	;	
			mem_top.mem_rlen 	[i]	= axi_arlen_i	;	
			mem_top.mem_rsize	[i] 	= axi_arsize_i	;	
			mem_top.mem_rburst[i] 	= axi_arburst_i ;	
			mem_top.mem_rlock	[i] 	= axi_arlock_i	;	
			mem_top.mem_rcache[i] 	= axi_arcache_i ;	
			mem_top.mem_rprot	[i] 	= axi_arprot_i	;
			mem_top.mem_rQOS	[i] 	= axi_arQOS_i	;
			mem_top.mem_rregion[i] 	= axi_arregion_i;
			mem_top.mem_ruser[i] 	= axi_aruser_i  ;		
			i = i+1;
		end
	end
end
endmodule

