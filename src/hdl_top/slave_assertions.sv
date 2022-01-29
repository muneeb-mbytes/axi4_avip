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
                            input                     awready,
                            //Read Address Channel
                            input              [3: 0] arid,     
                            input [ADDRESS_WIDTH-1:0] araddr,  
                            input               [7:0] arlen,      
                            input               [2:0] arsize,     
                            input               [1:0] arburst,    
                            input               [1:0] arlock,     
                            input               [3:0] arcache,    
                            input               [2:0] arprot,     
                            input               [3:0] arqos,      
                            input               [3:0] arregion,   
                            input               [3:0] aruser,     
                            input                     arvalid,    
 	                          input	                    arready);


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
  //Description: All signals must remain stable after ARVALID is asserted until ARREADY IS LOW
  property if_read_address_channel_signals_are_stable(logic arid, logic araddr, logic arlen, logic arsize,
                                                       logic arburst, logic arlock, logic arcache, logic arprot);
    @(posedge aclk) disable iff (!aresetn)
    (arvalid==1 && arready==0) |-> ($stable(arid) && $stable(araddr) && $stable(arlen) && $stable(arsize) && 
                                    $stable(arburst) && $stable(arlock) && $stable(arcache) && $stable(arprot));
  endproperty : if_read_address_channel_signals_are_stable
  AXI_RA_STABLE_SIGNALS_CHECK: assert property (if_read_address_channel_signals_are_stable(arid,araddr,arlen,arsize,
                                                                                            arburst,arlock,arcache,arprot));
 
  //Assertion: AXI_RA_UNKNOWN_SIGNALS_CHECK
  //Description: A value of X on signals is not permitted when ARVALID is HIGH
  property if_read_address_channel_signals_are_unknown(logic arid, logic araddr, logic arlen, logic arsize,
                                                       logic arburst, logic arlock, logic arcache, logic arprot);
    @(posedge aclk) disable iff (!aresetn)
    (arvalid==1) |-> (!($isunknown(arid)) && !($isunknown(araddr)) && !($isunknown(arlen)) && !($isunknown(arsize))
                     && !($isunknown(arburst)) && !($isunknown(arlock)) && !($isunknown(arcache)) && !($isunknown(arprot)));
  endproperty : if_read_address_channel_signals_are_unknown
  AXI_RA_UNKNOWN_SIGNALS_CHECK: assert property (if_read_address_channel_signals_are_unknown(arid,araddr,arlen,arsize,
                                                                                              arburst,arlock,arcache,arprot));

  //Assertion: AXI_RA_VALID_STABLE_CHECK
  //When ARVALID is asserted, then it must remain asserted until ARREADY is HIGH
  property axi_ra_valid_stable_check;
    @(posedge aclk) disable iff (!aresetn)
    $rose(arvalid) |-> arvalid s_until_with arready;
  endproperty : axi_ra_valid_stable_check
  AXI_RA_VALID_STABLE_CHECK : assert property (axi_ra_valid_stable_check);

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

