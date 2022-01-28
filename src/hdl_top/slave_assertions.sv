`ifndef SLAVE_ASSERTIONS_INCLUDED_
`define SLAVE_ASSERTIONS_INCLUDED_

//-------------------------------------------------------
// Importing Global Package
//-------------------------------------------------------
import axi4_globals_pkg::*;

//--------------------------------------------------------------------------------------------
// Interface : slave_assertions
// Used to write the assertion checks required for the slave checks
//--------------------------------------------------------------------------------------------
interface slave_assertions (input                     aclk,
                            input                     aresetn,
                            //Write_address_channel
                            input               [3:0] awid,
                            input [ADDRESS_WIDTH-1:0] awaddr ,
                            input               [3:0] awlen,
                            input               [2:0] awsize,
                            input               [1:0] awburst,
                            input               [1:0] awlock,
                            input               [3:0] awcache,
                            input               [2:0] awprot,
                            input                     awvalid,
                            input                     awready);

  //-------------------------------------------------------
  // Importing Uvm Package
  //-------------------------------------------------------
  import uvm_pkg::*;
  `include "uvm_macros.svh";

  initial begin
    `uvm_info("SLAVE_ASSERTIONS","SLAVE_ASSERTIONS",UVM_LOW);
  end
  
  //--------------------------------------------------------------------------------------------
  // Assertion properties written for various checks in write address channel
  //--------------------------------------------------------------------------------------------
  
  //Assertion: AXI_WA_STABLE_SIGNALS_CHECK
  //Description: All signals must remain stable after AWVALID is asserted until AWREADY IS LOW
  property if_write_address_channel_signals_are_stable(logic awid, logic awaddr, logic awlen, logic awsize,
                                                       logic awburst, logic awlock, logic awcache, logic awprot);
    @(posedge aclk) disable iff (!aresetn)
    (awvalid==1 && awready==0) |-> ($stable(awid) && $stable(awaddr) && $stable(awlen) && $stable(awsize) && 
                                    $stable(awburst) && $stable(awlock) && $stable(awcache) && $stable(awprot));
  endproperty : if_write_address_channel_signals_are_stable
  AXI_WA_STABLE_SIGNALS_CHECK: assert property (if_write_address_channel_signals_are_stable(awid,awaddr,awlen,awsize,
                                                                                            awburst,awlock,awcache,awprot));
 
  //Assertion: AXI_WA_UNKNOWN_SIGNALS_CHECK
  //Description: A value of X on signals is not permitted when AWVALID is HIGH
  property if_write_address_channel_signals_are_unknown(logic awid, logic awaddr, logic awlen, logic awsize,
                                                       logic awburst, logic awlock, logic awcache, logic awprot);
    @(posedge aclk) disable iff (!aresetn)
    (awvalid==1) |-> (!($isunknown(awid)) && !($isunknown(awaddr)) && !($isunknown(awlen)) && !($isunknown(awsize))
                     && !($isunknown(awburst)) && !($isunknown(awlock)) && !($isunknown(awcache)) && !($isunknown(awprot)));
  endproperty : if_write_address_channel_signals_are_unknown
  AXI_WA_UNKNOWN_SIGNALS_CHECK: assert property (if_write_address_channel_signals_are_unknown(awid,awaddr,awlen,awsize,
                                                                                              awburst,awlock,awcache,awprot));

  //Assertion: AXI_WA_VALID_STABLE_CHECK
  //When AWVALID is asserted, then it must remain asserted until AWREADY is HIGH
  property axi_wa_valid_stable_check;
    @(posedge aclk) disable iff (!aresetn)
    $rose(awvalid) |-> awvalid s_until_with awready;
  endproperty : axi_wa_valid_stable_check
  AXI_WA_VALID_STABLE_CHECK : assert property (axi_wa_valid_stable_check);


  //--------------------------------------------------------------------------------------------
  // Assertion properties written for various checks in write data channel
  //--------------------------------------------------------------------------------------------
  
  //Assertion: AXI_WD_STABLE_SIGNALS_CHECK
  //Description: All signals must remain stable after AWVALID is asserted until AWREADY IS LOW
 
  //Assertion: AXI_WD_UNKNOWN_SIGNALS_CHECK
  //Description: A value of X on signals is not permitted when AWVALID is HIGH

  //Assertion: AXI_WD_VALID_STABLE_CHECK
  //When AWVALID is asserted, then it must remain asserted until AWREADY is HIGH
  
  
  //--------------------------------------------------------------------------------------------
  // Assertion properties written for various checks in write response channel
  //--------------------------------------------------------------------------------------------
  
  //Assertion: AXI_WR_STABLE_SIGNALS_CHECK
  //Description: All signals must remain stable after AWVALID is asserted until AWREADY IS LOW
 
  //Assertion: AXI_WR_UNKNOWN_SIGNALS_CHECK
  //Description: A value of X on signals is not permitted when AWVALID is HIGH

  //Assertion: AXI_WR_VALID_STABLE_CHECK
  //When AWVALID is asserted, then it must remain asserted until AWREADY is HIGH

  
  //--------------------------------------------------------------------------------------------
  // Assertion properties written for various checks in read address channel
  //--------------------------------------------------------------------------------------------
  
  //Assertion: AXI_RA_STABLE_SIGNALS_CHECK
  //Description: All signals must remain stable after AWVALID is asserted until AWREADY IS LOW
 
  //Assertion: AXI_RA_UNKNOWN_SIGNALS_CHECK
  //Description: A value of X on signals is not permitted when AWVALID is HIGH

  //Assertion: AXI_RA_VALID_STABLE_CHECK
  //When AWVALID is asserted, then it must remain asserted until AWREADY is HIGH
  
  
  //--------------------------------------------------------------------------------------------
  // Assertion properties written for various checks in read data channel
  //--------------------------------------------------------------------------------------------
  
  //Assertion: AXI_RD_STABLE_SIGNALS_CHECK
  //Description: All signals must remain stable after AWVALID is asserted until AWREADY IS LOW
 
  //Assertion: AXI_RD_UNKNOWN_SIGNALS_CHECK
  //Description: A value of X on signals is not permitted when AWVALID is HIGH

  //Assertion: AXI_RD_VALID_STABLE_CHECK
  //When AWVALID is asserted, then it must remain asserted until AWREADY is HIGH

endinterface : slave_assertions

`endif

