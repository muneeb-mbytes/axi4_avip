//--------------------------------------------------------------------------------------------
// Module : Master Assertions_TB
// Used to write the assertion checks needed for the master
//--------------------------------------------------------------------------------------------
`ifndef TB_MASTER_ASSERTIONS_INCLUDED_
`define TB_MASTER_ASSERTIONS_INCLUDED_

import axi4_globals_pkg::*;
`include "uvm_macros.svh"
import uvm_pkg::*;

module tb_master_assertions;
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

  string name = "Master_assertions Tb";

  initial begin
    `uvm_info(name,$sformatf("TEST_BENCH FOR ASSERTIONS"),UVM_HIGH);
    //Include this to verify if signals are stable
    //if_addr_signals_are_stable_positive();
    //if_addr_signals_are_stable_negative();
    //signal_unknown_positive();
    //signal_unknown_negative_1();
    //signal_unknown_negative_2();
    //signal_unknown_negative_3();
    //signal_unknown_negative_4();
    valid_stable_pos();
  end

   task if_addr_signals_are_stable_positive();
      bit     [3: 0] awid_data     ;
      bit     [ADDRESS_WIDTH-1: 0] awaddr_data ;
      bit     [3: 0] awlen_data     ;
      bit     [2: 0] awsize_data    ;
      `uvm_info(name,$sformatf("INSIDE TASK"),UVM_HIGH);

    // random address data
    @(posedge aclk);
    awid_data = $urandom;
    awaddr_data = $urandom;
    awlen_data = $urandom;
    awsize_data = $urandom;
    
    
    awvalid = 1'b1;
    awready = 1'b0;

    //Driving address signals data
    while(awvalid == 1'b1 && !awready) begin
      
      @(posedge aclk);
      //Use this for negative scenario
      //awid_data = $urandom;
      //awaddr_data = $urandom;
      //awlen_data = $urandom;
      //awsize_data = $urandom;

      `uvm_info(name,$sformatf("INSIDE WHILE LOOP"),UVM_HIGH);
      awid = awid_data;
      awaddr = awaddr_data;
      awlen = awlen_data;
      awsize = awsize_data;
    end

  endtask 

   task if_addr_signals_are_stable_negative();
      bit     [3: 0] awid_data     ;
      bit     [ADDRESS_WIDTH-1: 0] awaddr_data ;
      bit     [3: 0] awlen_data     ;
      bit     [2: 0] awsize_data    ;
      `uvm_info(name,$sformatf("INSIDE TASK"),UVM_HIGH);
      awvalid = 1'b1;
      awready = 1'b0;

    //Driving address signals data
    while(awvalid == 1'b1 && !awready) begin
      @(posedge aclk);
      awid_data = $urandom;
      awaddr_data = $urandom;
      awlen_data = $urandom;
      awsize_data = $urandom;

      `uvm_info(name,$sformatf("INSIDE WHILE LOOP"),UVM_HIGH);
      awid = awid_data;
      awaddr = awaddr_data;
      awlen = awlen_data;
      awsize = awsize_data;
    end

  endtask 






  task signal_unknown_positive();
    bit     [3: 0] awid_data     ;
    bit     [ADDRESS_WIDTH-1: 0] awaddr_data ;
    bit     [3: 0] awlen_data     ;
    bit     [2: 0] awsize_data    ; 
    
    

    awvalid = 1'b1; 
    //Driving address signals data
    while(awvalid == 1'b1) begin
      awid_data = $urandom;
      awaddr_data = $urandom;
      awlen_data = $urandom;
      awsize_data = $urandom;
      
      awid = awid_data;
      awaddr = awaddr_data;
      awlen = awlen_data;
      awsize = awsize_data;
      @(posedge aclk); 
    end
endtask : signal_unknown_positive
  
  task signal_unknown_negative_1();
    bit     [3: 0] awid_data     ;
    bit     [ADDRESS_WIDTH-1: 0] awaddr_data ;
    bit     [3: 0] awlen_data     ;
    bit     [2: 0] awsize_data    ; 
    
    
    awid_data = $urandom;
    awaddr_data = $urandom;
    awlen_data = $urandom;
    awsize_data = $urandom;
    awvalid = 1'b1; 
    //Driving address signals data
    while(awvalid == 1'b1) begin
      @(posedge aclk);
      `uvm_info(name,$sformatf("INSIDE WHILE LOOP::UNKNOWN_SIGNALS_NEG"),UVM_HIGH);
      awid = 'bx;
      awaddr = awaddr_data;
      awlen = awlen_data;
      awsize = awsize_data;
    end
  endtask : signal_unknown_negative_1

  task signal_unknown_negative_2();
    bit     [3: 0] awid_data     ;
    bit     [ADDRESS_WIDTH-1: 0] awaddr_data ;
    bit     [3: 0] awlen_data     ;
    bit     [2: 0] awsize_data    ; 
    
    
    awid_data = $urandom;
    awaddr_data = $urandom;
    awlen_data = $urandom;
    awsize_data = $urandom;
    awvalid = 1'b1; 
    //Driving address signals data
    while(awvalid == 1'b1) begin
      @(posedge aclk);
      `uvm_info(name,$sformatf("INSIDE WHILE LOOP::UNKNOWN_SIGNALS_NEG"),UVM_HIGH);
      awid = awid_data;
      awaddr = 'bx;
      awlen = awlen_data;
      awsize = awsize_data;
    end
  endtask : signal_unknown_negative_2
  
  task signal_unknown_negative_3();
    bit     [3: 0] awid_data     ;
    bit     [ADDRESS_WIDTH-1: 0] awaddr_data ;
    bit     [3: 0] awlen_data     ;
    bit     [2: 0] awsize_data    ; 
    
    
    awid_data = $urandom;
    awaddr_data = $urandom;
    awlen_data = $urandom;
    awsize_data = $urandom;
    awvalid = 1'b1; 
    //Driving address signals data
    while(awvalid == 1'b1) begin
      @(posedge aclk);
      `uvm_info(name,$sformatf("INSIDE WHILE LOOP::UNKNOWN_SIGNALS_NEG"),UVM_HIGH);
      awid = 'bx;
      awaddr = awaddr_data;
      awlen = 'bx;
      awsize = awsize_data;
    end
  endtask : signal_unknown_negative_3

  task signal_unknown_negative_4();
    bit     [3: 0] awid_data     ;
    bit     [ADDRESS_WIDTH-1: 0] awaddr_data ;
    bit     [3: 0] awlen_data     ;
    bit     [2: 0] awsize_data    ; 
    
    
    awid_data = $urandom;
    awaddr_data = $urandom;
    awlen_data = $urandom;
    awsize_data = $urandom;
    awvalid = 1'b1; 
    //Driving address signals data
    while(awvalid == 1'b1) begin
      @(posedge aclk);
      `uvm_info(name,$sformatf("INSIDE WHILE LOOP::UNKNOWN_SIGNALS_NEG"),UVM_HIGH);
      awid = 'bx;
      awaddr = awaddr_data;
      awlen = awlen_data;
      awsize = 'bz;
    end
  endtask : signal_unknown_negative_4

  task valid_stable_pos();
    @(posedge aclk);
    awvalid = 1'b1;
    awready = 1'b0;

    //if(awvalid == 1 && awready == 0) begin
      `uvm_info(name,$sformatf("awvalid=%0d,awready=%0d",awvalid,awready),UVM_HIGH);
      awvalid = 1'b1;
      #120 ;
      awready = 1;
      `uvm_info(name,$sformatf("awvalid=%0d,awready=%0d",awvalid,awready),UVM_HIGH);
    //end

    //awvalid = $urandom;
    //awready = $urandom;
    $monitor("awvalid=%0d,awready=%0d",awvalid,awready);
  endtask : valid_stable_pos


  master_assertions M_A (.aclk(aclk),
                         .aresetn(aresetn),
                         .awid(awid),
                         .awaddr(awaddr),
                         .awlen(awlen),
                         .awsize(awsize),
                         .awburst(awburst),
                         .awlock(awlock),
                         //.awcache(awcache),
                         .awprot(awprot),
                         .awvalid(awvalid),
                         .awready(awready));
endmodule

`endif

