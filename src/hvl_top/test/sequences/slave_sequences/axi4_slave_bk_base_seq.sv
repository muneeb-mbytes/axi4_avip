`ifndef AXI4_SLAVE_BK_BASE_SEQ_INCLUDED_
`define AXI4_SLAVE_BK_BASE_SEQ_INCLUDED_

//--------------------------------------------------------------------------------------------
// Class: axi4_slave_bk_base_seq 
// creating axi4_slave_bk_base_seq class extends from uvm_sequence
//--------------------------------------------------------------------------------------------
class axi4_slave_bk_base_seq extends uvm_sequence #(axi4_slave_tx);
  //factory registration
  `uvm_object_utils(axi4_slave_bk_base_seq)
  //`uvm_declare_p_sequencer(axi4_slave_write_sequencer)
  // `uvm_declare_p_sequencer(axi4_slave_read_sequencer)
  
  //-------------------------------------------------------
  // Externally defined Function
  //-------------------------------------------------------
  extern function new(string name = "axi4_slave_bk_base_seq");
  extern task body();
endclass : axi4_slave_bk_base_seq

//-----------------------------------------------------------------------------
// Constructor: new
// Initializes the axi4_slave_sequence class object
//
// Parameters:
//  name - instance name of the config_template
//-----------------------------------------------------------------------------
function axi4_slave_bk_base_seq::new(string name = "axi4_slave_bk_base_seq");
  super.new(name);
endfunction : new

task axi4_slave_bk_base_seq::body();
//  if(!$cast(p_sequencer,m_sequencer))begin
//    `uvm_error(get_full_name(),"slave_agent_config pointer cast failed")
//  end
  req = axi4_slave_tx::type_id::create("req");
  req.transfer_type=BLOCKING_WRITE;
  req.transfer_type=BLOCKING_READ;
endtask

`endif
