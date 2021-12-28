`ifndef AXI4_VIRTUAL_SEQ_BASE_INCLUDED_
`define AXI4_VIRTUAL_SEQ_BASE_INCLUDED_

//--------------------------------------------------------------------------------------------
//Class: axi4_virtual_seq_base
// Description:
// This class contains the handle of actual sequencer pointing towards them
//--------------------------------------------------------------------------------------------
class axi4_virtual_seq_base extends uvm_sequence#(uvm_sequence_item);
  `uvm_object_utils(axi4_virtual_seq_base)

   //p sequencer macro declaration 
   `uvm_declare_p_sequencer(virtual_sequencer)
  
  //--------------------------------------------------------------------------------------------
  // Externally defined tasks and functions
  //--------------------------------------------------------------------------------------------
  extern function new(string name="axi4_virtual_seq_base");
  extern task body();

endclass:axi4_virtual_seq_base

//--------------------------------------------------------------------------------------------
//Constructor:new
//
//Paramters:
//name - Instance name of the virtual_sequence
//parent - parent under which this component is created
//--------------------------------------------------------------------------------------------
function axi4_virtual_seq_base::new(string name="axi4_virtual_seq_base");
  super.new(name);
endfunction:new

//--------------------------------------------------------------------------------------------
//task:body
//Creates the required ports
//
//Parameters:
// phase - stores the current phase
//--------------------------------------------------------------------------------------------
task axi4_virtual_seq_base::body();

endtask:body

`endif
