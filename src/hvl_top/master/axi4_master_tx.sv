`ifndef AXI4_MASTER_TX_INCLUDED_
`define AXI4_MASTER_TX_INCLUDED_

//--------------------------------------------------------------------------------------------
// Class: axi4_master_tx
// Description of the class
// This class holds the data items required to drive stimulus to dut
// and also holds methods that manipulate those data items
//--------------------------------------------------------------------------------------------
class axi4_master_tx extends uvm_sequence_item;
  
  //register with factory so we can override with uvm method in future if necessary.

  `uvm_object_utils(axi4_master_tx)

  //-------------------------------------------------------
  // Externally defined Tasks and Functions
  //-------------------------------------------------------
  extern function new(string name = "axi4_master_tx");
  extern function void do_copy(uvm_object rhs);
  extern function bit do_compare(uvm_object rhs, uvm_comparer comparer);
  extern function void do_print(uvm_printer printer);
endclass : axi4_master_tx

//--------------------------------------------------------------------------------------------
//  Construct: new
//  initializes the class object
//
//  Parameters:
//  name - axi4_master_tx
//--------------------------------------------------------------------------------------------
function axi4_master_tx::new(string name = "axi4_master_tx");
  super.new(name);
endfunction : new

//--------------------------------------------------------------------------------------------
// do_copy method
//--------------------------------------------------------------------------------------------

function void axi4_master_tx::do_copy (uvm_object rhs);
super.do_copy(rhs);
endfunction : do_copy

//--------------------------------------------------------------------------------------------
//  Function: do_compare
//  Compare method is implemented using handle rhs
//
//  Parameters:
//  phase - uvm phase
//--------------------------------------------------------------------------------------------
function bit axi4_master_tx::do_compare (uvm_object rhs, uvm_comparer comparer);
  axi4_master_tx axi_master_tx_compare_obj;

  if(!$cast(axi_master_tx_compare_obj,rhs)) begin
    `uvm_fatal("FATAL_axi_MASTER_TX_DO_COMPARE_FAILED","cast of the rhs object failed")
  return 0;
  end

endfunction:do_compare

//--------------------------------------------------------------------------------------------
// Function: do_print method
// Print method can be added to display the data members values
//--------------------------------------------------------------------------------------------
function void axi4_master_tx::do_print(uvm_printer printer);
  super.do_print(printer);

endfunction : do_print

`endif

