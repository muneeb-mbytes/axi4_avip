`ifndef AXI4_VIRTUAL_SEQ_PKG_INCLUDED_
`define AXI4_VIRTUAL_SEQ_PKG_INCLUDED_

//-----------------------------------------------------------------------------------------
// Package: axi4_virtual_seq_pkg
// Description:
// Includes all the files written to run the simulation
//-------------------------------------------------------------------------------------------
package axi4_virtual_seq_pkg;

  //-------------------------------------------------------
  // Import uvm package
  //-------------------------------------------------------
  `include "uvm_macros.svh"
  import uvm_pkg::*;
  import axi4_master_pkg::*;
  import axi4_slave_pkg::*; 
  import axi4_master_seq_pkg::*; 
  import axi4_slave_seq_pkg::*; 
  import axi4_env_pkg::*; 

  //-------------------------------------------------------
  // Importing the required packages
  //-------------------------------------------------------
  `include "axi4_virtual_base_seq.sv"
  `include "axi4_virtual_write_seq.sv"
  `include "axi4_virtual_read_seq.sv"
  `include "axi4_virtual_write_read_seq.sv"
  `include "axi4_virtual_bk_write_read_seq.sv"
  `include "axi4_virtual_nbk_write_read_seq.sv"

endpackage : axi4_virtual_seq_pkg

`endif

