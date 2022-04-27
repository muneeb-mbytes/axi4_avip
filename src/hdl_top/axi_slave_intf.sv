`ifndef AXI_SLAVE_INTF_INCLUDED_
`define AXI_SLAVE_INTF_INCLUDED_

//--------------------------------------------------------------------------------------------
// Interface : axi_slave_interface
// Declaration of pin level signals for axi slave interface
//--------------------------------------------------------------------------------------------

interface axi_slave_intf(input logic a1_clk);
   logic [31:0] sys_addr_o;
   logic [7:0] sys_wdata_o;
   logic [31:0] sys_sel_o;
   logic sys_wen_o;
   logic sys_ren_o;
   logic [7:0] sys_rdata_i;
   logic sys_err_i;      
   logic sys_ack_i;  
endinterface: axi_slave_intf

`endif

