`ifndef AXI4_VIRTUAL_nbk_INCR_BURST_READ_SEQ_INCLUDED_
`define AXI4_VIRTUAL_nbk_INCR_BURST_READ_SEQ_INCLUDED_

//--------------------------------------------------------------------------------------------
// Class: axi4_virtual_nbk_incr_burst_read_seq
// Creates and starts the master and slave sequences
//--------------------------------------------------------------------------------------------
class axi4_virtual_nbk_incr_burst_read_seq extends axi4_virtual_base_seq;
  `uvm_object_utils(axi4_virtual_nbk_incr_burst_read_seq)

  //Variable: axi4_master_write_seq_h
  //Instantiation of axi4_master_write_seq handle
//  axi4_master_nbk_write_seq axi4_master_nbk_write_seq_h;
  //axi4_master_nnbk_write_seq axi4_master_nnbk_write_seq_h;
  axi4_master_nbk_read_incr_burst_seq axi4_master_nbk_read_incr_burst_seq_h;
//  axi4_master_nnbk_read_seq axi4_master_nnbk_read_seq_h;

  //Variable: axi4_slave_write_seq_h
  //Instantiation of axi4_slave_write_seq handle
  //axi4_slave_nbk_write_seq axi4_slave_nbk_write_seq_h;
  //axi4_slave_nnbk_write_seq axi4_slave_nnbk_write_seq_h;
  axi4_slave_nbk_read_incr_burst_seq axi4_slave_nbk_read_incr_burst_seq_h;
 // axi4_slave_nnbk_read_seq axi4_slave_nnbk_read_seq_h;

  //-------------------------------------------------------
  // Externally defined Tasks and Functions
  //-------------------------------------------------------
  extern function new(string name = "axi4_virtual_nbk_incr_burst_read_seq");
  extern task body();
endclass : axi4_virtual_nbk_incr_burst_read_seq

//--------------------------------------------------------------------------------------------
// Construct: new
// Initialises new memory for the object
//
// Parameters:
//  name - axi4_virtual_nbk_incr_burst_read_seq
//--------------------------------------------------------------------------------------------
function axi4_virtual_nbk_incr_burst_read_seq::new(string name = "axi4_virtual_nbk_incr_burst_read_seq");
  super.new(name);
endfunction : new

//--------------------------------------------------------------------------------------------
// Task - body
// Creates and starts the data of master and slave sequences
//--------------------------------------------------------------------------------------------
task axi4_virtual_nbk_incr_burst_read_seq::body();
 // axi4_master_nbk_write_seq_h = axi4_master_nbk_write_seq::type_id::create("axi4_master_nbk_write_seq_h");
  //axi4_master_nnbk_write_seq_h = axi4_master_nnbk_write_seq::type_id::create("axi4_master_nnbk_write_seq_h");
  axi4_master_nbk_read_incr_burst_seq_h = axi4_master_nbk_read_incr_burst_seq::type_id::create("axi4_master_nbk_read_incr_burst_seq_h");
  //axi4_master_nincr_burst_read_seq_h = axi4_master_nincr_burst_read_seq::type_id::create("axi4_master_nincr_burst_read_seq_h");

 // axi4_slave_nbk_write_seq_h = axi4_slave_nbk_write_seq::type_id::create("axi4_slave_nbk_write_seq_h");
  //axi4_slave_nnbk_write_seq_h = axi4_slave_nnbk_write_seq::type_id::create("axi4_slave_nnbk_write_seq_h");
  axi4_slave_nbk_read_incr_burst_seq_h =
  axi4_slave_nbk_read_incr_burst_seq::type_id::create("axi4_slave_nbk_read_incr_burst_seq_h");
  //axi4_slave_nincr_burst_read_seq_h = axi4_slave_nincr_burst_read_seq::type_id::create("axi4_slave_nincr_burst_read_seq_h");

  `uvm_info(get_type_name(), $sformatf("DEBUG_MSHA :: Insdie axi4_virtual_nbk_read_incr_burst_seq"), UVM_NONE); 

  fork 
  //  begin : T1_SL_WR
  //    forever begin
  //  //  axi4_slave_nbk_write_seq_h.start(p_sequencer.axi4_slave_write_seqr_h);
  //  //    axi4_slave_nnbk_write_seq_h.start(p_sequencer.axi4_slave_write_seqr_h);
  //    end
  //  end
    begin : T2_SL_RD
      forever begin
        axi4_slave_nbk_read_incr_burst_seq_h.start(p_sequencer.axi4_slave_read_seqr_h);
      //  axi4_slave_nincr_burst_read_seq_h.start(p_sequencer.axi4_slave_read_seqr_h);
      end
    end
  join_none


  fork 
 //   begin: T1_WRITE
 //     repeat(2) begin
 //     //  axi4_master_nbk_write_seq_h.start(p_sequencer.axi4_master_write_seqr_h);
 //      //   axi4_master_nnbk_write_seq_h.start(p_sequencer.axi4_master_write_seqr_h);
 //     end
 //   end
    begin: T2_READ
      repeat(3) begin
      axi4_master_nbk_read_incr_burst_seq_h.start(p_sequencer.axi4_master_read_seqr_h);
     // axi4_master_nread_incr_burst_seq_h.start(p_sequencer.axi4_master_read_seqr_h);
      end
    end
  join
 endtask : body

`endif
