interface axi_slave_intf(input logic a1_clk,logic rst);
   logic [31:0] sys_addr_o;
   logic [7:0] sys_wdata_o;
   logic [31:0] sys_sel_o;
   logic sys_wen_o;
   logic sys_ren_o;
   logic [7:0] sys_rdata_i;
endinterface

