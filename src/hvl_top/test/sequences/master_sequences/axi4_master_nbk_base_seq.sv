`ifndef AXI4_MASTER_NBK_BASE_SEQ_INCLUDED_
`define AXI4_MASTER_NBK_BASE_SEQ_INCLUDED_

//--------------------------------------------------------------------------------------------
// Class: axi4_master_nbk_base_seq 
// creating axi4_master_nbk_base_seq class extends from uvm_sequence
//--------------------------------------------------------------------------------------------
class axi4_master_nbk_base_seq extends uvm_sequence #(axi4_master_tx);
  //factory registration
  `uvm_object_utils(axi4_master_nbk_base_seq)
  //`uvm_declare_p_sequencer(axi4_master_write_sequencer)
  // `uvm_declare_p_sequencer(axi4_master_read_sequencer)
  
  //-------------------------------------------------------
  // Externally defined Function
  //-------------------------------------------------------
  extern function new(string name = "axi4_master_nbk_base_seq");
  extern task body();
endclass : axi4_master_nbk_base_seq

//-----------------------------------------------------------------------------
// Constructor: new
// Initializes the axi4_master_sequence class object
//
// Parameters:
//  name - instance name of the config_template
//-----------------------------------------------------------------------------
function axi4_master_nbk_base_seq::new(string name = "axi4_master_nbk_base_seq");
  super.new(name);
endfunction : new

task axi4_master_nbk_base_seq::body();
//  if(!$cast(p_sequencer,m_sequencer))begin
//    `uvm_error(get_full_name(),"master_agent_config pointer cast failed")
  req = axi4_master_tx::type_id::create("req");
  req.transfer_type = NON_BLOCKING_WRITE ;
  req.transfer_type = NON_BLOCKING_READ ;
//  end
endtask

`endif
