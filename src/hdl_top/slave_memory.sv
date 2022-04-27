//------------------------------------------------------------------------------
// module name: mem_slave
// Slave Memory used to store the data
//------------------------------------------------------------------------------
module mem_slave(
  input sys_clk,
  input [31:0]sys_addr,
  input [7:0]sys_wdata,
  input [31:0]sys_sel,
  input sys_wen,
  input sys_ren,
  output reg [7:0]sys_rdata,
  output reg sys_err,
  output reg sys_ack
);

// slave memory
reg [7:0] mem[2000000:0];

//-------------------------------------------------------
// write block
//-------------------------------------------------------
always@(posedge sys_clk)begin
	if(sys_wen)begin
		#0.5	mem[sys_addr] <= sys_wdata;
    sys_err <= 0;
	end
end

//-------------------------------------------------------
// read block
//-------------------------------------------------------
always@(negedge sys_clk)begin
	if(sys_ren)begin
		sys_rdata <= mem[sys_addr];
	end
end

endmodule

