`ifndef AXI4_TEST_PKG_INCLUDED_
`define AXI4_TEST_PKG_INCLUDED_

//-----------------------------------------------------------------------------------------
// Package: Test
// Description:
// Includes all the files written to run the simulation
//--------------------------------------------------------------------------------------------
package axi4_test_pkg;

  //-------------------------------------------------------
  // Import uvm package
  //-------------------------------------------------------
  `include "uvm_macros.svh"
  import uvm_pkg::*;
  import axi4_globals_pkg::*;
  import axi4_master_pkg::*;
  import axi4_slave_pkg::*;
  import axi4_env_pkg::*;
  import axi4_master_seq_pkg::*;
  import axi4_slave_seq_pkg::*;
  import axi4_virtual_seq_pkg::*;


  //including base_test for testing
  `include "axi4_base_test.sv"

endpackage : axi4_test_pkg

`endif
