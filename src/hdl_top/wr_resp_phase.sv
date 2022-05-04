import axi4_globals_pkg::*;

module wr_resp_phase#(
parameter           AXI_DW         =  DATA_WIDTH   ,
parameter           AXI_AW         =  32           ,
parameter           AXI_IW         =   4           ,
parameter           AXI_SW         = AXI_DW >> 3   , 
parameter	          AXI_SI	       =   5
)
(
   input                     axi_clk_i     ,
   input                     axi_rstn_i    ,
   output reg [ AXI_IW-1: 0] axi_bid_o     ,
   output reg [2-1: 0]       axi_bresp_o   ,
   output reg [4-1: 0]       axi_buser_o   ,
   output reg                axi_bvalid_o  ,
   input		     axi_bready_i  
);

  reg [ AXI_IW-1: 0] bid; 
  reg[3:0] i = 0;

always@(posedge axi_clk_i)begin
	if(!axi_rstn_i)begin
		axi_bresp_o <= 2'bz;
		axi_bvalid_o = 0;
	end
	else begin
       //         bid = $urandom;  
       //         if(bid == axi_top_slave.mem_wid[i])begin     
                      axi_bid_o  <=  axi_top_slave.mem_wid[i];
			                    axi_bresp_o <= 2'b00;
                          axi_buser_o <= 4'b00;
			                    axi_bvalid_o = 1;
                          i++;
		              end
                end
endmodule








