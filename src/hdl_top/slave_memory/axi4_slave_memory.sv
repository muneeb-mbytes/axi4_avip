`ifndef AXI4_SLAVE_MEMORY
`define AXI4_SLAVE_MEMORY

module axi4_slave_memory(
input sys_clk,
input rst,
input [31:0]sys_addr,
input [7:0]sys_wdata,
input [31:0]sys_sel,
input sys_wen,
input sys_ren,
output reg [7:0]sys_rdata
);
reg [7:0] mem[2000000:0];

always@(posedge sys_clk)begin
  if(rst) begin 
	  if(sys_wen)begin
		  mem[sys_addr] = sys_wdata;
	  end
	end
end
always@(negedge sys_clk)begin
 if(rst) begin 
	 if(sys_ren)begin
		sys_rdata <= mem[sys_addr];
	 end
 end
end
endmodule
`endif
