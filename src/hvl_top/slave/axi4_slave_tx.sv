`ifndef AXI4_SLAVE_TX_INCLUDED_
`define AXI4_SLAVE_TX_INCLUDED_

//--------------------------------------------------------------------------------------------
// Class: axi4_slave_tx
// Description of the class
// This class holds the data items required to drive stimulus to dut
// and also holds methods that manipulate those data items
//--------------------------------------------------------------------------------------------
class axi4_slave_tx extends uvm_sequence_item;
  
  //register with factory so we can override with uvm method in future if necessary.

  `uvm_object_utils(axi4_slave_tx)

  //-------------------------------------------------------
  // Externally defined Tasks and Functions
  //-------------------------------------------------------
  extern function new(string name = "axi4_slave_tx");
  extern function void do_copy(uvm_object rhs);
  extern function void do_print(uvm_printer printer);
endclass : axi4_slave_tx

//--------------------------------------------------------------------------------------------
//  Construct: new
//  initializes the class object
//
//  Parameters:
//  name - axi4_slave_tx
//--------------------------------------------------------------------------------------------
function axi4_slave_tx::new(string name = "axi4_slave_tx");
  super.new(name);
endfunction : new

//--------------------------------------------------------------------------------------------
// do_copy method
//--------------------------------------------------------------------------------------------

function void axi4_slave_tx::do_copy (uvm_object rhs);

  super.do_copy(rhs);
endfunction : do_copy


//--------------------------------------------------------------------------------------------
// Function: do_print method
// Print method can be added to display the data members values
//--------------------------------------------------------------------------------------------
function void axi4_slave_tx::do_print(uvm_printer printer);
  super.do_print(printer);

endfunction : do_print

`endif

