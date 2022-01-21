`ifndef AXI4_SLAVE_SEQ_PKG_INCLUDED_
`define AXI4_SLAVE_SEQ_PKG_INCLUDED_

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
  `include "axi4_slave_write_seq.sv"
  `include "axi4_slave_read_seq.sv"
  `include "axi4_slave_bk_base_seq.sv"
  `include "axi4_slave_bk_write_seq.sv"
  `include "axi4_slave_bk_read_seq.sv"
  `include "axi4_slave_nbk_base_seq.sv"
  `include "axi4_slave_nbk_write_seq.sv"
  `include "axi4_slave_nbk_read_seq.sv"

endpackage : axi4_slave_seq_pkg

`endif

