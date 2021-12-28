`ifndef AXI4_SLAVE_SEQ_ITEM_CONVERTER_INCLUDED_
`define AXI4_SLAVE_SEQ_ITEM_CONVERTER_INCLUDED_

//--------------------------------------------------------------------------------------------
// Class: axi4_slave_seq_item_converter
// Description:
// class for converting the transaction items to struct and vice versa
//--------------------------------------------------------------------------------------------
class axi4_slave_seq_item_converter extends uvm_object;
  `uvm_object_utils(axi4_slave_seq_item_converter)

  //-------------------------------------------------------
  // Externally defined Tasks and Functions
  //-------------------------------------------------------
  extern function new(string name = "axi4_slave_seq_item_converter");
  extern function void do_print(uvm_printer printer);
endclass : axi4_slave_seq_item_converter

//--------------------------------------------------------------------------------------------
// Construct: new
//
// Parameters:
// name - axi4_slave_seq_item_converter
//--------------------------------------------------------------------------------------------
function axi4_slave_seq_item_converter::new(string name = "axi4_slave_seq_item_converter");
  super.new(name);
endfunction : new


//--------------------------------------------------------------------------------------------
// Function: do_print method
// Print method can be added to display the data members values
//--------------------------------------------------------------------------------------------
function void axi4_slave_seq_item_converter::do_print(uvm_printer printer);
  super.do_print(printer);
endfunction : do_print

`endif
