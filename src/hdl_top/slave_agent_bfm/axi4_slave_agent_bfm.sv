`ifndef AXI4_SLAVE_AGENT_BFMNCLUDED_
`define AXI4_SLAVE_AGENT_BFMNCLUDED_

//--------------------------------------------------------------------------------------------
// Module:AXI4 Slave Agent BFM
// This module is used as the configuration class for slave agent bfm and its components
//--------------------------------------------------------------------------------------------
module axi4_slave_agent_bfm #(parameter int SLAVE_ID = 0)(axi4_if intf);

  //-------------------------------------------------------
  // Package : Importing Uvm Pakckage and Test Package
  //-------------------------------------------------------
  import uvm_pkg::*;
  `include "uvm_macros.svh"
  
  //-------------------------------------------------------
  // AXI4 Slave Driver bfm instantiation
  //-------------------------------------------------------
  axi4_slave_driver_bfm axi4_slave_drv_bfm_h (.aclk     (intf.aclk)     , 
                                              .aresetn  (intf.aresetn)  ,
                                              .awid     (intf.awid)     ,           
                                              .awaddr   (intf.awaddr)   ,  
                                              .awlen    (intf.awlen)    ,   
                                              .awsize   (intf.awsize)   ,  
                                              .awburst  (intf.awburst)  , 
                                              .awlock   (intf.awlock)   ,  
                                              .awcache  (intf.awcache)  , 
                                              .awprot   (intf.awprot)   ,  
                                              .awvalid  (intf.awvalid)  , 
                                              .awready  (intf.awready)  , 
                                                                            
                                              .wdata    (intf.wdata)    ,   
                                              .wstrb    (intf.wstrb)    ,   
                                              .wlast    (intf.wlast)    ,   
                                              .wuser    (intf.wuser)    ,   
                                              .wvalid   (intf.wvalid)   ,  
                                              .wready   (intf.wready)   ,  
                                                              
                                              .bid      (intf.bid)      ,    
                                              .bresp    (intf.bresp)    ,   
                                              .buser    (intf.buser)    ,   
                                              .bvalid   (intf.bvalid)   ,  
                                              .bready   (intf.bready)   ,  
                                                                            
                                              .arid     (intf.arid)     ,    
                                              .araddr   (intf.araddr)   ,  
                                              .arlen    (intf.arlen)    ,   
                                              .arsize   (intf.arsize)   ,  
                                              .arburst  (intf.arburst)  , 
                                              .arlock   (intf.arlock)   ,  
                                              .arcache  (intf.arcache)  , 
                                              .arprot   (intf.arprot)   ,  
                                              .arQOS    (intf.arQOS)    ,   
                                              .arregion (intf.arregion) ,
                                              .aruser   (intf.aruser)   ,  
                                              .arvalid  (intf.arvalid)  , 
                                              .arready  (intf.arready)  , 
                                                                            
                                              .rid      (intf.rid)      ,     
                                              .rdata    (intf.rdata)    ,   
                                              .rstrb    (intf.rstrb)    ,   
                                              .rresp    (intf.rresp)    ,   
                                              .rlast    (intf.rlast)    ,   
                                              .ruser    (intf.ruser)    ,   
                                              .rvalid   (intf.rvalid)   ,  
                                              .rready   (intf.rready)   
                                              );
  //-------------------------------------------------------
  // AXI4 Slave monitor  bfm instantiation
  //-------------------------------------------------------
  axi4_slave_monitor_bfm axi4_slave_mon_bfm_h (.aclk(intf.aclk), 
                                       .aresetn(intf.aresetn)
                                     );

  //-------------------------------------------------------
  // Setting the virtual handle of BMFs into config_db
  //-------------------------------------------------------
  initial begin
    uvm_config_db#(virtual axi4_slave_driver_bfm)::set(null,"*", "axi4_slave_driver_bfm", axi4_slave_drv_bfm_h); 
    uvm_config_db#(virtual axi4_slave_monitor_bfm)::set(null,"*", "axi4_slave_monitor_bfm", axi4_slave_mon_bfm_h);
  end

  //Printing axi4 slave agent bfm
  initial begin
    `uvm_info("axi4 slave agent bfm",$sformatf("AXI4 SLAVE AGENT BFM"),UVM_LOW);
  end
   
endmodule : axi4_slave_agent_bfm
`endif
