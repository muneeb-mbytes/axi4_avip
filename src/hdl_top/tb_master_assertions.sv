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
    //Include this to verify if signals are stable
    if_addr_signals_are_stable();
    signal_unknown_pos();
  end

   task if_addr_signals_are_stable();
      logic     [3: 0] awid_data     ;
      logic     [ADDRESS_WIDTH-1: 0] awaddr_data ;
      logic     [3: 0] awlen_data     ;
      logic     [2: 0] awsize_data    ;

    // random address data
    awid_data = $urandom;
    awaddr_data = $urandom;
    awlen_data = $urandom;
    awsize_data = $urandom;
    
    //Driving address signals data
    while(awvalid == 1'b1) begin
      @(posedge aclk);
      awid = awid_data;
      awaddr = awaddr_data;
      awlen = awlen_data;
      awsize = awsize_data;
    end

  endtask 



  task signal_unknown_pos();
    logic     [3: 0] awid_data     ;
    logic     [ADDRESS_WIDTH-1: 0] awaddr_data ;
    logic     [3: 0] awlen_data     ;
    logic     [2: 0] awsize_data    ; 
    
    
    awid_data = $urandom;
    awaddr_data = $urandom;
    awlen_data = $urandom;
    awsize_data = $urandom;
    
    //Driving address signals data
    while(awvalid == 1'b1) begin
      @(posedge aclk);
      awid = awid_data;
      awaddr = awaddr_data;
      awlen = awlen_data;
      awsize = awsize_data;
    end
endtask : signal_unknown_pos
  

  task valid_stable_pos();
    @(posedge aclk)
    awvalid=$urandom;
    awready=$urandom;
  endtask : valid_stable_pos


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

