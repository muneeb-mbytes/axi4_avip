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
  //Write Address Channel Signals
  logic               [3:0] awid;
  logic [ADDRESS_WIDTH-1:0] awaddr;
  logic               [3:0] awlen;
  logic               [2:0] awsize;
  logic               [1:0] awburst;
  logic               [1:0] awlock;
  logic               [3:0] awcache;
  logic               [2:0] awprot;
  logic                     awvalid;
  logic                     awready;
  //Write Data Channel Signals
  //Write Response Channel Signal  
  logic     [3: 0] bid       ;
  logic     [1: 0] bresp     ;
  logic     [3: 0] buser     ;
  logic            bvalid    ;
  logic            bready    ;
  //Read Address Channel Signals
  logic               [3:0] arid;
  logic [ADDRESS_WIDTH-1:0] araddr;
  logic               [7:0] arlen;
  logic               [2:0] arsize;
  logic               [1:0] arburst;
  logic               [1:0] arlock;
  logic               [3:0] arcache;
  logic               [2:0] arprot;
  logic               [3:0] arqos;
  logic               [3:0] arregion;
  logic               [3:0] aruser;
  logic                     arvalid;
  logic	                    arready;
  //Read Data Channel Signals
  logic            [3:0] rid;
  logic [DATA_WIDTH-1:0] rdata;
  logic            [1:0] rresp;
  logic                  rlast;
  logic            [3:0] ruser;
  logic                  rvalid;
  logic                  rready;

  
  //Variable: MASTER_ASSERTIONS_TB
  //Declaring MASTER_ASSERTIONS_TB as string 'name'
  string name = "MASTER_ASSERTIONS_TB";

  //-------------------------------------------------------
  // Including all the tasks for verification of various scenarios
  //-------------------------------------------------------
  initial begin
    `uvm_info(name,$sformatf("TEST_BENCH_FOR_MASTER_ASSERTIONS"),UVM_LOW);
    
    //-------------------------------------------------------
    // Include these tasks to verify positive scenarios 
    // for the assertions in testbench
    //-------------------------------------------------------
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
    
    //-------------------------------------------------------
    // Include these tasks to verify negative scenarios 
    // for the assertions in testbench
    //-------------------------------------------------------
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
  // Task: if_wa_channel_valid_stable_positive_case
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
  // Task: if_wa_channel_valid_stable_negative_case
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

  //-------------------------------------------------------
  // Task: if_wr_channel_signals_are_stable_positive_case
  //-------------------------------------------------------
  task if_wr_channel_signals_are_stable_positive_case();
       
    bit [3:0]bid_local;
    bit [2:0]buser_local;
    bit [2:0]bresp_local;
    bit [1:0]delay_local;
    
    //Calling task aresetn_gen()
    aresetn_gen();
     
    repeat(6) begin

      delay_local = $urandom;
  
      repeat(delay_local) begin
        @(posedge aclk);
      end

      @(posedge aclk);
      //Randomizing the signals
      bid_local      = $urandom;
      buser_local    = $urandom;
      bresp_local    = $urandom;

      bid            <= bid_local;
      buser          <= buser_local;
      bresp          <= bresp_local;
      bvalid         <= 1'b1;
      bready         <= 1'b0;

      repeat(delay_local) begin
        @(posedge aclk);
      end

      bvalid         <= 1'b1;
      bready         <= 1'b1;

      repeat(delay_local) begin
        @(posedge aclk);
      end

      bvalid         <= 1'b0;
      bready         <= 1'b0;
      `uvm_info(name,$sformatf("if_wr_channel_signals_are_stable_positive_case-- INSIDE REPEAT"),UVM_HIGH);
    end

  endtask : if_wr_channel_signals_are_stable_positive_case

  //-------------------------------------------------------
  // Task: if_wr_channel_signals_are_stable_negative_case
  //-------------------------------------------------------
  task if_wr_channel_signals_are_stable_negative_case();

    bit [3:0]bid_local;
    bit [2:0]buser_local;
    bit [2:0]bresp_local;
    bit [1:0]delay_local;
    
    //Calling task aresetn_gen()
    aresetn_gen();
     
    repeat(6) begin

      delay_local = $urandom;
  
      repeat(delay_local) begin
        @(posedge aclk);
      end

      bid            = $urandom;
      buser          = $urandom;
      bresp          = $urandom;
      bvalid         = 1'b1;
      bready         = 1'b0;

      repeat(delay_local) begin
        @(posedge aclk);
        bid            = $urandom;
        buser          = $urandom;
        bresp          = $urandom;
      end

      bvalid         = 1'b1;
      bready         = 1'b1;

      repeat(delay_local) begin
        @(posedge aclk);
      end

      bvalid         = 1'b0;
      bready         = 1'b0;
      `uvm_info(name,$sformatf("if_wr_channel_signals_are_stable_negative_case-- INSIDE REPEAT"),UVM_HIGH);

    end
  endtask : if_wr_channel_signals_are_stable_negative_case
    
  //-------------------------------------------------------
  // Task: if_wr_channel_signals_are_unknown_positive_case
  //-------------------------------------------------------
  task if_wr_channel_signals_are_unknown_positive_case();

    bit [3:0]bid_local;
    bit [2:0]buser_local;
    bit [2:0]bresp_local;
    bit [1:0]delay_local;
    
    //Calling task aresetn_gen()
    aresetn_gen();
     
    repeat(6) begin

      @(posedge aclk);
      delay_local = $urandom;
      bvalid         = 1'b0;
  
      repeat(delay_local) begin
        @(posedge aclk);
      end
      
      bid            = $urandom;
      buser          = $urandom;
      bresp          = $urandom;
      bvalid         = 1'b1;

      `uvm_info(name,$sformatf("if_wr_channel_signals_are_unknown_positive_case-- INSIDE REPEAT"),UVM_HIGH);

    end

  endtask : if_wr_channel_signals_are_unknown_positive_case

  //-------------------------------------------------------
  // Task: if_wr_channel_signals_are_unknown_negative_case
  //-------------------------------------------------------
  task if_wr_channel_signals_are_unknown_negative_case();

    bit [3:0]bid_local;
    bit [2:0]buser_local;
    bit [2:0]bresp_local;
    bit [1:0]delay_local;
    
    //Calling task aresetn_gen()
    aresetn_gen();
     
    repeat(6) begin

      @(posedge aclk);
      delay_local = $urandom;
      bvalid         = 1'b0;
  
      repeat(delay_local) begin
        @(posedge aclk);
      end
      
      bid            = 'bx;
      buser          = 'bx;
      bresp          = 'bz;
      bvalid         = 1'b1;

      `uvm_info(name,$sformatf("if_wr_channel_signals_are_unknown_negative_case-- INSIDE REPEAT"),UVM_HIGH);

    end

  endtask : if_wr_channel_signals_are_unknown_negative_case
  
  //-------------------------------------------------------
  // Task: if_wr_channel_valid_stable_positive_case
  //-------------------------------------------------------
  task if_wr_channel_valid_stable_positive_case();

    bit [1:0]delay_local;
    
    //Calling task aresetn_gen()
    aresetn_gen();
     
    repeat(6) begin

      @(posedge aclk);
      delay_local     = $urandom;
      bvalid         <= 1'b0;
      bready         <= 1'b0;
  
      repeat(delay_local) begin
        @(posedge aclk);
      end
      
      bvalid         <= 1'b1;
      bready         <= 1'b0;

      repeat(delay_local) begin
        @(posedge aclk);
      end

      bvalid         <= 1'b1;
      bready         <= 1'b1;

      //@(posedge aclk);
      //bvalid         <= 1'b0;
      //bready         <= 1'b0;

      `uvm_info(name,$sformatf("if_wr_channel_valid_stable_positive_case-- INSIDE REPEAT"),UVM_HIGH);
    end

  endtask : if_wr_channel_valid_stable_positive_case

  //-------------------------------------------------------
  // Task: if_wr_channel_valid_stable_negative_case
  //-------------------------------------------------------
  task if_wr_channel_valid_stable_negative_case();

    bit [1:0]delay_local;
    
    //Calling task aresetn_gen()
    aresetn_gen();
     
    repeat(6) begin

      @(posedge aclk);
      delay_local     = $urandom;
      bvalid         <= 1'b0;
      bready         <= 1'b0;
  
      repeat(delay_local) begin
        @(posedge aclk);
      end
      
      bvalid         <= 1'b1;
      bready         <= 1'b0;

      repeat(delay_local) begin
        @(posedge aclk);
      end

      bvalid         <= 1'b0;
      bready         <= 1'b0;

      repeat(delay_local) begin
        @(posedge aclk);
      end
      bvalid         <= 1'b0;
      bready         <= 1'b1;

      @(posedge aclk);
      bvalid        <= 1'b0;
      bready        <= 1'b0;

      `uvm_info(name,$sformatf("if_wr_channel_valid_stable_negative_case-- INSIDE REPEAT"),UVM_HIGH);
    
    end

  endtask : if_wr_channel_valid_stable_negative_case
    
  //--------------------------------------------------------------------------------------------
  // Tasks written to verify assertions for read_address_channel
  //--------------------------------------------------------------------------------------------
  //-------------------------------------------------------
  // Task: if_ra_channel_signals_are_stable_positive_case
  //-------------------------------------------------------
  task if_ra_channel_signals_are_stable_positive_case();
    bit               [3:0] arid_data;
    bit [ADDRESS_WIDTH-1:0] araddr_data;
    bit               [3:0] arlen_data;
    bit               [2:0] arsize_data;
    bit               [1:0] arburst_data;
    bit               [1:0] arlock_data;
    bit               [3:0] arcache_data;
    bit               [2:0] arprot_data;
    
    //Calling task aresetn_gen()
    aresetn_gen();
    
    //Randomizing the signals
    @(posedge aclk);
    arid_data    = $urandom;
    araddr_data  = $urandom;
    arlen_data   = $urandom;
    arsize_data  = $urandom;
    arburst_data = $urandom;
    arlock_data  = $urandom;
    arcache_data = $urandom;
    arprot_data  = $urandom;
    arvalid      = 1'b1;
    arready      = 1'b0;

    //Driving address signals data
    while(arvalid==1 && arready==0) begin
      @(posedge aclk);
      `uvm_info(name,$sformatf("if_ra_channel_signals_are_stable_positive_case::INSIDE WHILE LOOP"),UVM_HIGH);
      arid    = arid_data;
      araddr  = araddr_data;
      arlen   = arlen_data;
      arsize  = arsize_data;
      arburst = arburst_data;
      arlock  = arlock_data;
      arcache = arcache_data;
      arprot  = arprot_data;
    end
  endtask : if_ra_channel_signals_are_stable_positive_case

  //-------------------------------------------------------
  // Task: if_ra_channel_signals_are_stable_negative_case
  //-------------------------------------------------------
  task if_ra_channel_signals_are_stable_negative_case();
    bit               [3:0] arid_data;
    bit [ADDRESS_WIDTH-1:0] araddr_data;
    bit               [3:0] arlen_data;
    bit               [2:0] arsize_data;
    bit               [1:0] arburst_data;
    bit               [1:0] arlock_data;
    bit               [3:0] arcache_data;
    bit               [2:0] arprot_data;
    
    //Calling task aresetn_gen()
    aresetn_gen();
   
    //Randomizing the signals
    @(posedge aclk);
    arvalid = 1'b1;
    arready = 1'b0;

    //Driving address signals data
    while(arvalid==1 && arready==0) begin
      @(posedge aclk);
      `uvm_info(name,$sformatf("if_ra_channel_signals_are_stable_negative_case::INSIDE WHILE LOOP"),UVM_HIGH);
      arid_data    = $urandom;
      araddr_data  = $urandom;
      arlen_data   = $urandom;
      arsize_data  = $urandom;
      arburst_data = $urandom;
      arlock_data  = $urandom;
      arcache_data = $urandom;
      arprot_data  = $urandom;
      arid         = arid_data;
      araddr       = araddr_data;
      arlen        = arlen_data;
      arsize       = arsize_data;
      arburst      = arburst_data;
      arlock       = arlock_data;
      arcache      = arcache_data;
      arprot       = arprot_data;
    end
  endtask : if_ra_channel_signals_are_stable_negative_case

  //-------------------------------------------------------
  // Task: if_ra_channel_signals_are_unknown_positive_case
  //-------------------------------------------------------
  task if_ra_channel_signals_are_unknown_positive_case();
    bit               [3:0] arid_data;
    bit [ADDRESS_WIDTH-1:0] araddr_data;
    bit               [3:0] arlen_data;
    bit               [2:0] arsize_data;
    bit               [1:0] arburst_data;
    bit               [1:0] arlock_data;
    bit               [3:0] arcache_data;
    bit               [2:0] arprot_data;
    
    //Calling task aresetn_gen()
    aresetn_gen();
    
    //Randomizing the signals
    @(posedge aclk);
    arvalid = 1'b1;

    //Driving address signals data
    while(arvalid==1) begin
      @(posedge aclk);
      `uvm_info(name,$sformatf("if_ra_channel_signals_are_unknown_positive_case::INSIDE WHILE LOOP"),UVM_HIGH);
      arid_data    = $urandom;
      araddr_data  = $urandom;
      arlen_data   = $urandom;
      arsize_data  = $urandom;
      arburst_data = $urandom;
      arlock_data  = $urandom;
      arcache_data = $urandom;
      arprot_data  = $urandom;
      arid         = arid_data;
      araddr       = araddr_data;
      arlen        = arlen_data;
      arsize       = arsize_data;
      arburst      = arburst_data;
      arlock       = arlock_data;
      arcache      = arcache_data;
      arprot       = arprot_data;
    end
  endtask : if_ra_channel_signals_are_unknown_positive_case

  //-------------------------------------------------------
  // Task: if_ra_channel_signals_are_unknown_negative_case
  //-------------------------------------------------------
  task if_ra_channel_signals_are_unknown_negative_case();
    bit               [3:0] arid_data;
    bit [ADDRESS_WIDTH-1:0] araddr_data;
    bit               [3:0] arlen_data;
    bit               [2:0] arsize_data;
    bit               [1:0] arburst_data;
    bit               [1:0] arlock_data;
    bit               [3:0] arcache_data;
    bit               [2:0] arprot_data;
    
    //Calling task aresetn_gen()
    aresetn_gen();
    
    //Randomizing the signals
    @(posedge aclk);
    arid_data    = $urandom;
    araddr_data  = $urandom;
    arlen_data   = $urandom;
    arsize_data  = $urandom;
    arburst_data = $urandom;
    arlock_data  = $urandom;
    arcache_data = $urandom;
    arprot_data  = $urandom;
    arvalid      = 1'b1;
      
    //Driving address signals data
    while(arvalid==1) begin
      @(posedge aclk);
      `uvm_info(name,$sformatf("if_ra_channel_signals_are_unknown_negative_case::INSIDE WHILE LOOP"),UVM_HIGH);
      arid    = 1'bx; 
      araddr  = 1'bx; 
      arlen   = 1'bx; 
      arsize  = 1'bx; 
      arburst = 1'bx; 
      arlock  = 1'bx; 
      arcache = 1'bx; 
      arprot  = 1'bx; 
    end
  endtask : if_ra_channel_signals_are_unknown_negative_case

  //-------------------------------------------------------
  // Task: if_ra_channel_valid_stable_positive_case
  //-------------------------------------------------------
  task if_ra_channel_valid_stable_positive_case();
    @(posedge aclk);
    arvalid = 1'b1;
    arready = 1'b0;
    `uvm_info(name,$sformatf("arvalid=%0d,arready=%0d",arvalid,arready),UVM_HIGH);
    #60;
    arready = 1'b1;
    `uvm_info(name,$sformatf("arvalid=%0d,arready=%0d",arvalid,arready),UVM_HIGH);
  endtask : if_ra_channel_valid_stable_positive_case

  //-------------------------------------------------------
  // Task: if_ra_channel_valid_stable_negative_case
  //-------------------------------------------------------
  task if_ra_channel_valid_stable_negative_case();
    @(posedge aclk);
    arvalid = 1'b1;
    arready = 1'b0;
    `uvm_info(name,$sformatf("arvalid=%0d,arready=%0d",arvalid,arready),UVM_HIGH);
    #60;
    arvalid = 1'b0;
    `uvm_info(name,$sformatf("arvalid=%0d,arready=%0d",arvalid,arready),UVM_HIGH);
    #30;
    arready = 1'b1;
    `uvm_info(name,$sformatf("arvalid=%0d,arready=%0d",arvalid,arready),UVM_HIGH);
  endtask : if_ra_channel_valid_stable_negative_case


  //--------------------------------------------------------------------------------------------
  // Tasks written to verify assertions for read_data_channel
  //--------------------------------------------------------------------------------------------
  //-------------------------------------------------------
  // Task: if_rd_channel_signals_are_stable_positive_case
  //-------------------------------------------------------
  task if_rd_channel_signals_are_stable_positive_case();
    bit            [3:0] rid_data;
    bit [DATA_WIDTH-1:0] rdata_data;
    bit            [1:0] rresp_data;
    bit                  rlast_data;
    bit            [3:0] ruser_data;
    bit                  rvalid_data;
    bit                  rready_data;
    
    //Calling task aresetn_gen()
    aresetn_gen();
    
    //Randomizing the signals
    @(posedge aclk);
    rid_data   = $urandom; 
    rdata_data = $urandom; 
    rresp_data = $urandom; 
    rlast_data = $urandom; 
    ruser_data = $urandom; 
    rvalid     = 1'b1;
    rready     = 1'b0;

    //Driving address signals data
    while(rvalid==1 && rready==0) begin
      @(posedge aclk);
      `uvm_info(name,$sformatf("if_rd_channel_signals_are_stable_positive_case::INSIDE WHILE LOOP"),UVM_HIGH);
      rid   = rid_data; 
      rdata = rdata_data; 
      rresp = rresp_data; 
      rlast = rlast_data; 
      ruser = ruser_data; 
    end
  endtask : if_rd_channel_signals_are_stable_positive_case

  //-------------------------------------------------------
  // Task: if_rd_channel_signals_are_stable_negative_case
  //-------------------------------------------------------
  task if_rd_channel_signals_are_stable_negative_case();
    bit            [3:0] rid_data;
    bit [DATA_WIDTH-1:0] rdata_data;
    bit            [1:0] rresp_data;
    bit                  rlast_data;
    bit            [3:0] ruser_data;
    bit                  rvalid_data;
    bit                  rready_data;
    
    //Calling task aresetn_gen()
    aresetn_gen();
   
    //Randomizing the signals
    @(posedge aclk);
    rvalid = 1'b1;
    rready = 1'b0;

    //Driving address signals data
    while(rvalid==1 && rready==0) begin
      @(posedge aclk);
      `uvm_info(name,$sformatf("if_rd_channel_signals_are_stable_negative_case::INSIDE WHILE LOOP"),UVM_HIGH);
      rid_data   = $urandom; 
      rdata_data = $urandom; 
      rresp_data = $urandom; 
      rlast_data = $urandom; 
      ruser_data = $urandom; 
      rid        = rid_data; 
      rdata      = rdata_data; 
      rresp      = rresp_data; 
      rlast      = rlast_data; 
      ruser      = ruser_data; 
    end
  endtask : if_rd_channel_signals_are_stable_negative_case

  //-------------------------------------------------------
  // Task: if_rd_channel_signals_are_unknown_positive_case
  //-------------------------------------------------------
  task if_rd_channel_signals_are_unknown_positive_case();
    bit            [3:0] rid_data;
    bit [DATA_WIDTH-1:0] rdata_data;
    bit            [1:0] rresp_data;
    bit                  rlast_data;
    bit            [3:0] ruser_data;
    bit                  rvalid_data;
    bit                  rready_data;
    
    //Calling task aresetn_gen()
    aresetn_gen();
    
    //Randomizing the signals
    @(posedge aclk);
    rvalid = 1'b1;

    //Driving address signals data
    while(rvalid==1) begin
      @(posedge aclk);
      `uvm_info(name,$sformatf("if_rd_channel_signals_are_unknown_positive_case::INSIDE WHILE LOOP"),UVM_HIGH);
      rid_data   = $urandom; 
      rdata_data = $urandom; 
      rresp_data = $urandom; 
      rlast_data = $urandom; 
      ruser_data = $urandom; 
      rid        = rid_data; 
      rdata      = rdata_data; 
      rresp      = rresp_data; 
      rlast      = rlast_data; 
      ruser      = ruser_data; 
    end
  endtask : if_rd_channel_signals_are_unknown_positive_case

  //-------------------------------------------------------
  // Task: if_rd_channel_signals_are_unknown_negative_case
  //-------------------------------------------------------
  task if_rd_channel_signals_are_unknown_negative_case();
    bit            [3:0] rid_data;
    bit [DATA_WIDTH-1:0] rdata_data;
    bit            [1:0] rresp_data;
    bit                  rlast_data;
    bit            [3:0] ruser_data;
    bit                  rvalid_data;
    bit                  rready_data;
    
    //Calling task aresetn_gen()
    aresetn_gen();
    
    //Randomizing the signals
    @(posedge aclk);
    rid_data   = $urandom; 
    rdata_data = $urandom; 
    rresp_data = $urandom; 
    rlast_data = $urandom; 
    ruser_data = $urandom; 
    rvalid     = 1'b1;
      
    //Driving address signals data
    while(rvalid==1) begin
      @(posedge aclk);
      `uvm_info(name,$sformatf("if_rd_channel_signals_are_unknown_negative_case::INSIDE WHILE LOOP"),UVM_HIGH);
      rid   = 1'bx; 
      rdata = 1'bx; 
      rresp = 1'bx; 
      rlast = 1'bx; 
      ruser = 1'bx; 
    end
  endtask : if_rd_channel_signals_are_unknown_negative_case

  //-------------------------------------------------------
  // Task: if_rd_channel_valid_stable_positive_case
  //-------------------------------------------------------
  task if_rd_channel_valid_stable_positive_case();
    @(posedge aclk);
    rvalid = 1'b1;
    rready = 1'b0;
    `uvm_info(name,$sformatf("rvalid=%0d,rready=%0d",rvalid,rready),UVM_HIGH);
    #60;
    rready = 1'b1;
    `uvm_info(name,$sformatf("rvalid=%0d,rready=%0d",rvalid,rready),UVM_HIGH);
  endtask : if_rd_channel_valid_stable_positive_case

  //-------------------------------------------------------
  // Task: if_rd_channel_valid_stable_negative_case
  //-------------------------------------------------------
  task if_rd_channel_valid_stable_negative_case();
    @(posedge aclk);
    rvalid = 1'b1;
    rready = 1'b0;
    `uvm_info(name,$sformatf("rvalid=%0d,rready=%0d",rvalid,rready),UVM_HIGH);
    #60;
    rvalid = 1'b0;
    `uvm_info(name,$sformatf("rvalid=%0d,rready=%0d",rvalid,rready),UVM_HIGH);
    #30;
    rready = 1'b1;
    `uvm_info(name,$sformatf("rvalid=%0d,rready=%0d",rvalid,rready),UVM_HIGH);
  endtask : if_rd_channel_valid_stable_negative_case

  
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
                         .awready(awready),
                         .bid(bid),
                         .buser(buser),
                         .bvalid(bvalid),
                         .bready(bready),
                         .bresp(bresp),
                         .arid(arid),
                         .araddr(araddr),  
                         .arlen(arlen),   
                         .arsize(arsize), 
                         .arburst(arburst), 
                         .arlock(arlock),  
                         .arcache(arcache), 
                         .arprot(arprot),
                         .arqos(arqos),   
                         .arregion(arregion), 
                         .aruser(aruser),  
                         .arvalid(arvalid), 
                         .arready(arready),
                         .rid(rid),
                         .rdata(rdata),
                         .rresp(rresp),
                         .rlast(rlast),
                         .ruser(ruser),
                         .rvalid(rvalid),
                         .rready(rready)
                       );

endmodule : tb_master_assertions

`endif

