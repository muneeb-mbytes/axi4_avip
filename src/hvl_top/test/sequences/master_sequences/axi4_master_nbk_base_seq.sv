`ifndef AXI4_MASTER_NBK_BASE_SEQ_INCLUDED_
`define AXI4_MASTER_NBK_BASE_SEQ_INCLUDED_

//--------------------------------------------------------------------------------------------
// Class: axi4_master_nbk_base_seq 
// creating axi4_master_nbk_base_seq class extends from uvm_sequence
//--------------------------------------------------------------------------------------------
class axi4_master_nbk_base_seq extends uvm_sequence #(axi4_master_tx);
 
  //factory registration
  `uvm_object_utils(axi4_master_nbk_base_seq)

//  `uvm_declare_p_sequencer(axi4_master_agent)
    
//  axi4_master_agent_config  axi4_master_agent_h;
  
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

//-----------------------------------------------------------------------------
// Task: body
// based on the request from driver task will drive the transactions
//-----------------------------------------------------------------------------
task axi4_master_nbk_base_seq::body();
  req = axi4_master_tx::type_id::create("req");
//  axi4_master_agent_h = axi4_master_agent_config::type_id::create("axi4_master_agent_h");
//  if(!$cast(p_sequencer,m_sequencer))begin
//    `uvm_error(get_full_name(),"Virtual sequencer pointer cast failed")
//  end
  
 // req.axi4_master_agent_cfg_h = axi4_master_agent_h;
  req.transfer_type = NON_BLOCKING_WRITE ;
  req.transfer_type = NON_BLOCKING_READ ;

endtask : body

`endif
