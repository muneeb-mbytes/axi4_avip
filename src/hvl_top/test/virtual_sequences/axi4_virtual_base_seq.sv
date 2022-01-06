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
 
   axi4_master_write_sequencer  axi4_master_write_seqr_h;
   axi4_master_read_sequencer  axi4_master_read_seqr_h;
   axi4_slave_sequencer  axi4_slave_seqr_h;

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
  if(!$cast(p_sequencer,m_sequencer))begin
    `uvm_error(get_full_name(),"Virtual sequencer pointer cast failed")
  end
    axi4_slave_seqr_h  = p_sequencer.axi4_slave_seqr_h;
    axi4_master_write_seqr_h = p_sequencer.axi4_master_write_seqr_h;
    axi4_master_read_seqr_h = p_sequencer.axi4_master_read_seqr_h;
endtask:body

`endif
