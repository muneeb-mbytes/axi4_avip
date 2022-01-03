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


  //Parameter : SLAVE_MEMORY_SIZE
  //Sets the memory size of the slave in KB
  parameter int SLAVE_MEMORY_SIZE = 12;

  //Parameter : SLAVE_MEMORY_GAP
  //Sets the memory gap size of the slave
  parameter int SLAVE_MEMORY_GAP = 4;

  //Parameter : MEMORY_WIDTH
  //Sets the width it can store in each loaction
  parameter int MEMORY_WIDTH = 8;


  //Parameter : SLAVE_AGENT_ACTIVE
  //Used to set the slave agent either active or passive
  parameter int SLAVE_AGENT_ACTIVE = 1;
endpackage: axi4_globals_pkg

`endif
