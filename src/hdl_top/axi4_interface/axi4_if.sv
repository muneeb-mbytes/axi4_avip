`ifndef AXI4_IF_INCLUDED_
`define AXI4_IF_INCLUDED_

// Import axi4_globals_pkg 
import axi4_globals_pkg::*;

//--------------------------------------------------------------------------------------------
// Interface : axi4_if
// Declaration of pin level signals for axi4 interface
//--------------------------------------------------------------------------------------------
interface axi4_if(input pclk, input aresetn);

  // Variable: aclk
  // axi4 clock signal
  bit aclk;
  

endinterface: axi4_if 

`endif
