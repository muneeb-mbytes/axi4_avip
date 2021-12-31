`ifndef AXI4_GLOBALS_PKG_INCLUDED_
`define AXI4_GLOBALS_PKG_INCLUDED_

//--------------------------------------------------------------------------------------------
// Package: axi4_globals_pkg
// Used for storing enums, parameters and defines
//--------------------------------------------------------------------------------------------
package axi4_globals_pkg;
  
  //Variable: AXI_DW
  //Indicates AXI  Data_bus width 
  parameter int AXI_DW         =  64;

  //Variable: AXI_AW
  //Indicates AXI Address width 
  parameter int AXI_AW         =  32;


  //Variable: AXI_IW
  //Indicates AXI ID width 
  parameter int AXI_IW         =   4;


  //Variable: AXI_SW
  //Indicates AXI Strobe width 
  parameter int AXI_SW         =  AXI_DW >> 3;

  //Variable: MEM_ID
  //Indicates Slave Memory Depth 
  parameter int MEM_ID         =   2**AXI_IW;

  parameter int NO_OF_MASTERS = 1;

  parameter int NO_OF_SLAVES = 1;


endpackage: axi4_globals_pkg

`endif
