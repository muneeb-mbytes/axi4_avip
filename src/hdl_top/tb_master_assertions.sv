`ifndef TB_MASTER_ASSERTIONS_INCLUDED_
`define TB_MASTER_ASSERTIONS_INCLUDED_

//-------------------------------------------------------
// Importing global package
//-------------------------------------------------------
import axi4_globals_pkg::*;

//-------------------------------------------------------
// Importing uvm package and including macros file
//-------------------------------------------------------
`include "uvm_macros.svh"
import uvm_pkg::*;

//--------------------------------------------------------------------------------------------
// Module : tb_master_assertions
// Used to write the assertion checks testbench required for the master assertion
//--------------------------------------------------------------------------------------------
module tb_master_assertions;
  bit                       aclk;
  bit                       aresetn;
  logic               [3:0] awid;
  logic [ADDRESS_WIDTH-1:0] awaddr ;
  logic               [3:0] awlen;
  logic               [2:0] awsize;
  logic               [1:0] awburst;
  logic               [1:0] awlock;
  logic               [3:0] awcache;
  logic               [2:0] awprot;
  logic                     awvalid;
  logic                     awready;
  
  //Variable: MASTER_ASSERTIONS_TB
  //Declaring MASTER_ASSERTIONS_TB as string 'name'
  string name = "MASTER_ASSERTIONS_TB";

  //-------------------------------------------------------
  // Including all the tasks for verification of various scenarios
  //-------------------------------------------------------
  initial begin
    `uvm_info(name,$sformatf("TEST_BENCH_FOR_MASTER_ASSERTIONS"),UVM_LOW);
    
    //Include these tasks to verify positive scenarios for the assertions in testbench
    //if_wa_channel_signals_are_stable_positive_case();
    //if_wa_channel_signals_are_unknown_positive_case();
    //if_wa_channel_valid_stable_positive_case();
    
    //if_wd_channel_signals_are_stable_positive_case();
    //if_wd_channel_signals_are_unknown_positive_case();
    //if_wd_channel_valid_stable_positive_case();

    //if_wr_channel_signals_are_stable_positive_case();
    //if_wr_channel_signals_are_unknown_positive_case();
    //if_wr_channel_valid_stable_positive_case();

    //if_ra_channel_signals_are_stable_positive_case();
    //if_ra_channel_signals_are_unknown_positive_case();
    //if_ra_channel_valid_stable_positive_case();

    //if_rd_channel_signals_are_stable_positive_case();
    //if_rd_channel_signals_are_unknown_positive_case();
    //if_rd_channel_valid_stable_positive_case();

    //Include these tasks to verify negative scenarios for the assertions in testbench
    //if_wa_channel_signals_are_stable_negative_case();
    //if_wa_channel_signals_are_unknown_negative_case();
    //if_wa_channel_valid_stable_negative_case();

    //if_wd_channel_signals_are_stable_negative_case();
    //if_wd_channel_signals_are_unknown_negative_case();
    //if_wd_channel_valid_stable_negative_case();
    
    //if_wr_channel_signals_are_stable_negative_case();
    //if_wr_channel_signals_are_unknown_negative_case();
    //if_wr_channel_valid_stable_negative_case();
    
    //if_ra_channel_signals_are_stable_negative_case();
    //if_ra_channel_signals_are_unknown_negative_case();
    //if_ra_channel_valid_stable_negative_case();
    
    //if_rd_channel_signals_are_stable_negative_case();
    //if_rd_channel_signals_are_unknown_negative_case();
    //if_rd_channel_valid_stable_negative_case();
  end

  //-------------------------------------------------------
  // Clock Generation
  //-------------------------------------------------------
  always #10 aclk = ~aclk;

  //-------------------------------------------------------
  // Task: Generating aresetn initially
  //-------------------------------------------------------
  task aresetn_gen();
    aresetn = 1'b0;
    repeat(1) begin
      @(posedge aclk); 
    end
    aresetn = 1'b1;
    `uvm_info(name,$sformatf("Generating_aresetn"),UVM_HIGH);
  endtask : aresetn_gen

  //--------------------------------------------------------------------------------------------
  // Tasks written to verify assertions for write_address_channel
  //--------------------------------------------------------------------------------------------
  //-------------------------------------------------------
  // Task: if_wa_channel_signals_are_stable_positive_case
  //-------------------------------------------------------
  task if_wa_channel_signals_are_stable_positive_case();
    bit               [3:0] awid_data;
    bit [ADDRESS_WIDTH-1:0] awaddr_data;
    bit               [3:0] awlen_data;
    bit               [2:0] awsize_data;
    bit               [1:0] awburst_data;
    bit               [1:0] awlock_data;
    bit               [3:0] awcache_data;
    bit               [2:0] awprot_data;
    
    //Calling task aresetn_gen()
    aresetn_gen();
    
    //Randomizing the signals
    @(posedge aclk);
    awid_data    = $urandom;
    awaddr_data  = $urandom;
    awlen_data   = $urandom;
    awsize_data  = $urandom;
    awburst_data = $urandom;
    awlock_data  = $urandom;
    awcache_data = $urandom;
    awprot_data  = $urandom;
    awvalid      = 1'b1;
    awready      = 1'b0;

    //Driving address signals data
    while(awvalid==1 && awready==0) begin
      @(posedge aclk);
      `uvm_info(name,$sformatf("if_wa_channel_signals_are_stable_positive_case::INSIDE WHILE LOOP"),UVM_HIGH);
      awid    = awid_data;
      awaddr  = awaddr_data;
      awlen   = awlen_data;
      awsize  = awsize_data;
      awburst = awburst_data;
      awlock  = awlock_data;
      awcache = awcache_data;
      awprot  = awprot_data;
    end
  endtask : if_wa_channel_signals_are_stable_positive_case

  //-------------------------------------------------------
  // Task: if_wa_channel_signals_are_stable_negative_case
  //-------------------------------------------------------
  task if_wa_channel_signals_are_stable_negative_case();
    bit               [3:0] awid_data;
    bit [ADDRESS_WIDTH-1:0] awaddr_data;
    bit               [3:0] awlen_data;
    bit               [2:0] awsize_data;
    bit               [1:0] awburst_data;
    bit               [1:0] awlock_data;
    bit               [3:0] awcache_data;
    bit               [2:0] awprot_data;
    
    //Calling task aresetn_gen()
    aresetn_gen();
   
    //Randomizing the signals
    @(posedge aclk);
    awvalid = 1'b1;
    awready = 1'b0;

    //Driving address signals data
    while(awvalid==1 && awready==0) begin
      @(posedge aclk);
      `uvm_info(name,$sformatf("if_wa_channel_signals_are_stable_negative_case::INSIDE WHILE LOOP"),UVM_HIGH);
      awid_data    = $urandom;
      awaddr_data  = $urandom;
      awlen_data   = $urandom;
      awsize_data  = $urandom;
      awburst_data = $urandom;
      awlock_data  = $urandom;
      awcache_data = $urandom;
      awprot_data  = $urandom;
      awid         = awid_data;
      awaddr       = awaddr_data;
      awlen        = awlen_data;
      awsize       = awsize_data;
      awburst      = awburst_data;
      awlock       = awlock_data;
      awcache      = awcache_data;
      awprot       = awprot_data;
    end
  endtask : if_wa_channel_signals_are_stable_negative_case

  //-------------------------------------------------------
  // Task: if_wa_channel_signals_are_unknown_positive_case
  //-------------------------------------------------------
  task if_wa_channel_signals_are_unknown_positive_case();
    bit               [3:0] awid_data;
    bit [ADDRESS_WIDTH-1:0] awaddr_data;
    bit               [3:0] awlen_data;
    bit               [2:0] awsize_data;
    bit               [1:0] awburst_data;
    bit               [1:0] awlock_data;
    bit               [3:0] awcache_data;
    bit               [2:0] awprot_data;
    
    //Calling task aresetn_gen()
    aresetn_gen();
    
    //Randomizing the signals
    @(posedge aclk);
    awvalid = 1'b1;

    //Driving address signals data
    while(awvalid==1) begin
      @(posedge aclk);
      `uvm_info(name,$sformatf("if_wa_channel_signals_are_unknown_positive_case::INSIDE WHILE LOOP"),UVM_HIGH);
      awid_data    = $urandom;
      awaddr_data  = $urandom;
      awlen_data   = $urandom;
      awsize_data  = $urandom;
      awburst_data = $urandom;
      awlock_data  = $urandom;
      awcache_data = $urandom;
      awprot_data  = $urandom;
      awid         = awid_data;
      awaddr       = awaddr_data;
      awlen        = awlen_data;
      awsize       = awsize_data;
      awburst      = awburst_data;
      awlock       = awlock_data;
      awcache      = awcache_data;
      awprot       = awprot_data;
    end
  endtask : if_wa_channel_signals_are_unknown_positive_case

  //-------------------------------------------------------
  // Task: if_wa_channel_signals_are_unknown_negative_case
  //-------------------------------------------------------
  task if_wa_channel_signals_are_unknown_negative_case();
    bit               [3:0] awid_data;
    bit [ADDRESS_WIDTH-1:0] awaddr_data;
    bit               [3:0] awlen_data;
    bit               [2:0] awsize_data;
    bit               [1:0] awburst_data;
    bit               [1:0] awlock_data;
    bit               [3:0] awcache_data;
    bit               [2:0] awprot_data;
    
    //Calling task aresetn_gen()
    aresetn_gen();
    
    //Randomizing the signals
    @(posedge aclk);
    awid_data    = $urandom;
    awaddr_data  = $urandom;
    awlen_data   = $urandom;
    awsize_data  = $urandom;
    awburst_data = $urandom;
    awlock_data  = $urandom;
    awcache_data = $urandom;
    awprot_data  = $urandom;
    awvalid      = 1'b1;
      
    //Driving address signals data
    while(awvalid==1) begin
      @(posedge aclk);
      `uvm_info(name,$sformatf("if_wa_channel_signals_are_unknown_negative_case::INSIDE WHILE LOOP"),UVM_HIGH);
      awid    = 1'bx; 
      awaddr  = 1'bx; 
      awlen   = 1'bx; 
      awsize  = 1'bx; 
      awburst = 1'bx; 
      awlock  = 1'bx; 
      awcache = 1'bx; 
      awprot  = 1'bx; 
    end
  endtask : if_wa_channel_signals_are_unknown_negative_case

  //-------------------------------------------------------
  // Task: wa_channel_valid_stable_positive_case
  //-------------------------------------------------------
  task if_wa_channel_valid_stable_positive_case();
    @(posedge aclk);
    awvalid = 1'b1;
    awready = 1'b0;
    `uvm_info(name,$sformatf("awvalid=%0d,awready=%0d",awvalid,awready),UVM_HIGH);
    #60;
    awready = 1'b1;
    `uvm_info(name,$sformatf("awvalid=%0d,awready=%0d",awvalid,awready),UVM_HIGH);
  endtask : if_wa_channel_valid_stable_positive_case

  //-------------------------------------------------------
  // Task: wa_channel_valid_stable_negative_case
  //-------------------------------------------------------
  task if_wa_channel_valid_stable_negative_case();
    @(posedge aclk);
    awvalid = 1'b1;
    awready = 1'b0;
    `uvm_info(name,$sformatf("awvalid=%0d,awready=%0d",awvalid,awready),UVM_HIGH);
    #60;
    awvalid = 1'b0;
    `uvm_info(name,$sformatf("awvalid=%0d,awready=%0d",awvalid,awready),UVM_HIGH);
    #30;
    awready = 1'b1;
    `uvm_info(name,$sformatf("awvalid=%0d,awready=%0d",awvalid,awready),UVM_HIGH);
  endtask : if_wa_channel_valid_stable_negative_case

  
  //--------------------------------------------------------------------------------------------
  // Tasks written to verify assertions for write_data_channel
  //--------------------------------------------------------------------------------------------
    //task if_wd_channel_signals_are_stable_positive_case();
    //endtask : if_wd_channel_signals_are_stable_positive_case
    //task if_wd_channel_signals_are_stable_negative_case();
    //endtask : if_wd_channel_signals_are_stable_negative_case
    
    //task if_wd_channel_signals_are_unknown_positive_case();
    //endtask : if_wd_channel_signals_are_unknown_positive_case
    //task if_wd_channel_signals_are_unknown_negative_case();
    //endtask : if_wd_channel_signals_are_unknown_negative_case
    
    //task if_wd_channel_valid_stable_positive_case();
    //endtask : if_wd_channel_valid_stable_positive_case
    //task if_wd_channel_valid_stable_negative_case();
    //endtask : if_wd_channel_valid_stable_negative_case
    

  //--------------------------------------------------------------------------------------------
  // Tasks written to verify assertions for write_response_channel
  //--------------------------------------------------------------------------------------------
    //task if_wr_channel_signals_are_stable_positive_case();
    //endtask : if_wr_channel_signals_are_stable_positive_case
    //task if_wr_channel_signals_are_stable_negative_case();
    //endtask : if_wr_channel_signals_are_stable_negative_case
    
    //task if_wr_channel_signals_are_unknown_positive_case();
    //endtask : if_wr_channel_signals_are_unknown_positive_case
    //task if_wr_channel_signals_are_unknown_negative_case();
    //endtask : if_wr_channel_signals_are_unknown_negative_case
    
    //task if_wr_channel_valid_stable_positive_case();
    //endtask : if_wr_channel_valid_stable_positive_case
    //task if_wr_channel_valid_stable_negative_case();
    //endtask : if_wr_channel_valid_stable_negative_case
    

  //--------------------------------------------------------------------------------------------
  // Tasks written to verify assertions for read_address_channel
  //--------------------------------------------------------------------------------------------
    //task if_ra_channel_signals_are_stable_positive_case();
    //endtask : if_ra_channel_signals_are_stable_positive_case
    //task if_ra_channel_signals_are_stable_negative_case();
    //endtask : if_ra_channel_signals_are_stable_negative_case
    
    //task if_ra_channel_signals_are_unknown_positive_case();
    //endtask : if_ra_channel_signals_are_unknown_positive_case
    //task if_ra_channel_signals_are_unknown_negative_case();
    //endtask : if_ra_channel_signals_are_unknown_negative_case
    
    //task if_ra_channel_valid_stable_positive_case();
    //endtask : if_ra_channel_valid_stable_positive_case
    //task if_ra_channel_valid_stable_negative_case();
    //endtask : if_ra_channel_valid_stable_negative_case
    

  //--------------------------------------------------------------------------------------------
  // Tasks written to verify assertions for read_data_channel
  //--------------------------------------------------------------------------------------------
    //task if_rd_channel_signals_are_stable_positive_case();
    //endtask : if_rd_channel_signals_are_stable_positive_case
    //task if_rd_channel_signals_are_stable_negative_case();
    //endtask : if_rd_channel_signals_are_stable_negative_case
    
    //task if_rd_channel_signals_are_unknown_positive_case();
    //endtask : if_rd_channel_signals_are_unknown_positive_case
    //task if_rd_channel_signals_are_unknown_negative_case();
    //endtask : if_rd_channel_signals_are_unknown_negative_case
    
    //task if_rd_channel_valid_stable_positive_case();
    //endtask : if_rd_channel_valid_stable_positive_case
    //task if_rd_channel_valid_stable_negative_case();
    //endtask : if_rd_channel_valid_stable_negative_case

  
  //Instantiation of assertions
  master_assertions M_A (.aclk(aclk),
                         .aresetn(aresetn),
                         .awid(awid),
                         .awaddr(awaddr),
                         .awlen(awlen),
                         .awsize(awsize),
                         .awburst(awburst),
                         .awlock(awlock),
                         .awcache(awcache),
                         .awprot(awprot),
                         .awvalid(awvalid),
                         .awready(awready));

endmodule : tb_master_assertions

`endif

