`ifndef AXI4_MASTER_NBK_WRITE_16B_TRANSFER_SEQ_INCLUDED_
`define AXI4_MASTER_NBK_WRITE_16B_TRANSFER_SEQ_INCLUDED_

//--------------------------------------------------------------------------------------------
// Class: axi4_master_nbk_write_16b_transfer_seq
// Extends the axi4_master_base_seq and randomises the req item
//--------------------------------------------------------------------------------------------
class axi4_master_nbk_write_16b_transfer_seq extends axi4_master_nbk_base_seq;
  `uvm_object_utils(axi4_master_nbk_write_16b_transfer_seq)

  //-------------------------------------------------------
  // Externally defined Tasks and Functions
  //-------------------------------------------------------
  extern function new(string name = "axi4_master_nbk_write_16b_transfer_seq");
  extern task body();
endclass : axi4_master_nbk_write_16b_transfer_seq

//--------------------------------------------------------------------------------------------
// Construct: new
// Initializes new memory for the object
//
// Parameters:
//  name - axi4_master_nbk_write_16b_transfer_seq
//--------------------------------------------------------------------------------------------
function axi4_master_nbk_write_16b_transfer_seq::new(string name = "axi4_master_nbk_write_16b_transfer_seq");
  super.new(name);
endfunction : new

//--------------------------------------------------------------------------------------------
// Task: body
// Creates the req of type master transaction and randomises the req
//--------------------------------------------------------------------------------------------
task axi4_master_nbk_write_16b_transfer_seq::body();
  super.body();
  req.transfer_type=NON_BLOCKING_WRITE;
    // MSHA: req.type = this.type;
    `uvm_info(get_type_name(), $sformatf("DEBUG_MSHA :: BEFORE axi4_master_nbk_write_16b_transfer_seq"), UVM_NONE); 

  start_item(req);
    if(!req.randomize() with {req.awsize == WRITE_2_BYTES;
                              req.tx_type == WRITE;
                              req.awburst == WRITE_FIXED;
                              req.transfer_type == NON_BLOCKING_WRITE;}) begin
    `uvm_fatal("axi4","Rand failed");
  end
  `uvm_info(get_type_name(), $sformatf("DEBUG_MSHA :: master_seq \n%s",req.sprint()), UVM_NONE); 
  //req.print();
  finish_item(req);
    `uvm_info(get_type_name(), $sformatf("DEBUG_MSHA :: AFTER axi4_master_nbk_write_16b_transfer_seq"), UVM_NONE); 

endtask : body

`endif
