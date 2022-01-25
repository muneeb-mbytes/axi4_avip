//--------------------------------------------------------------------------------------------
// Module : Master Assertions_TB
// Used to write the assertion checks needed for the master
//--------------------------------------------------------------------------------------------
`ifndef TB_MASTER_ASSERTIONS_INCLUDED_
`define TB_MASTER_ASSERTIONS_INCLUDED_

module tb_master_assertions;
  import axi4_globals_pkg::*;
   bit              aclk;
   bit              aresetn;
   logic     [3: 0] awid     ;
   logic     [ADDRESS_WIDTH-1: 0] awaddr ;
   logic     [3: 0] awlen     ;
   logic     [2: 0] awsize    ;
   logic     [1: 0] awburst   ;
   logic     [1: 0] awlock    ;
   logic     [3: 0] awcache   ;
   logic     [2: 0] awprot    ;
   logic            awvalid   ;
   logic		        awready   ;

  always #10 aclk = ~aclk;

  initial begin
    signal_unknown_pos();
  end
  task signal_unknown_pos();
    @(posedge aclk)
    awid=$urandom;
    awaddr=$urandom;
    awlen=$urandom;
    awsize=$urandom;
  endtask : signal_unknown_pos
  
  master_assertions M_A (.aclk(aclk),
                         .aresetn(aresetn),
                         .awid(awid),
                         .awaddr(awaddr),
                         .awlen(awlen),
                         .awsize(awsize),
                         .awburst(awburst),
                         .awlock(awlock),
                         .awcache(aecache),
                         .awprot(awprot),
                         .awvalid(awvalid),
                         .awready(awready));
endmodule

`endif

