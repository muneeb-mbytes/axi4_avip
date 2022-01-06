`ifndef AXI4_SLAVE_SEQ_PKG_INCLUDED
`define AXI4_SLAVE_SEQ_PKG_INCLUDED

//-----------------------------------------------------------------------------------------
// Package: axi4_slave_seq_pkg
// Description:
// Includes all the files written to run the simulation
//-------------------------------------------------------------------------------------------
package axi4_slave_seq_pkg;

  //-------------------------------------------------------
  // Import uvm package
  //-------------------------------------------------------
  `include "uvm_macros.svh"
  import uvm_pkg::*;
  import axi4_slave_pkg::*;
  import axi4_globals_pkg::*;

  //-------------------------------------------------------
  // Importing the required packages
  //-------------------------------------------------------
  `include "axi4_slave_base_seq.sv"
  `include "axi4_slave_read_seq.sv"
  `include "axi4_slave_write_seq.sv"


endpackage : axi4_slave_seq_pkg

`endif
