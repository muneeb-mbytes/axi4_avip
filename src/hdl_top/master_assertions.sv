//--------------------------------------------------------------------------------------------
// Module : Master Assertions
// Used to write the assertion checks needed for the master
//--------------------------------------------------------------------------------------------
`ifndef MASTER_ASSERTIONS_INCLUDED_
`define MASTER_ASSERTIONS_INCLUDED_

  //-------------------------------------------------------
  // Importing Uvm Package
  //-------------------------------------------------------
  import axi4_globals_pkg::*;

interface master_assertions (input            aclk,
                             input            aresetn,
                             //Write_address_channel
                             input     [3: 0] awid     ,
                             input     [ADDRESS_WIDTH-1: 0] awaddr ,
                             input     [3: 0] awlen     ,
                             input     [2: 0] awsize    ,
                             input     [1: 0] awburst   ,
                             input     [1: 0] awlock    ,
                             input     [3: 0] awcache   ,
                             input     [2: 0] awprot    ,
                             input            awvalid   ,
                             input		        awready   );

  //-------------------------------------------------------
  // Importing Uvm Package
  //-------------------------------------------------------
  import uvm_pkg::*;
  `include "uvm_macros.svh";

  initial begin
    `uvm_info("MASTER_ASSERTIONS","MASTER ASSERTIONS",UVM_LOW);
  end
  
  // Assertion for AXI_WA_STABLE_SIGNALS_CHECK

  // Assertion for AXI_WA_UNKNOWN_SIGNALS_CHECK

  // Assertion for AXI_WA_UNKNOWN_SIGNALS_CHECK, the signal should not be unknown when awvalid is high
  AXI_AWADDR_X : assert property(@(posedge aclk) awvalid -> (!$isunknown(awaddr)));
  AXI_AWLEN_X  : assert property(@(posedge aclk) awvalid -> (!$isunknown(awlen)));
  AXI_AWSIZE_X : assert property(@(posedge aclk) awvalid -> (!$isunknown(awsize)));
  AXI_AWID_X   : assert property(@(posedge aclk) awvalid -> (!$isunknown(awid)));


  // Assertion for AXI_WA_VALID_STABLE_CHECK 
  property axi_wa_valid_stable_check;
    @(posedge aclk) disable iff(!areset)
    awvalid == 1 |-> $stable(awvalid) && $rose(awready);
  endproperty : axi_wa_valid_stable_check

  AXI_WA_VALID_STABLE_CHECK : assert property(axi_wa_valid_stable_check);



endinterface : master_assertions

`endif
