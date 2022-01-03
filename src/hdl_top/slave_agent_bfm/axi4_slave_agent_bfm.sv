`ifndef AXI4_SLAVE_AGENT_BFM_INCLUDED_
`define AXI4_SLAVE_AGENT_BFM_INCLUDED_

//--------------------------------------------------------------------------------------------
// Module:AXI4 Slave Agent BFM
// This module is used as the configuration class for slave agent bfm and its components
//--------------------------------------------------------------------------------------------
module axi4_slave_agent_bfm #(parameter int SLAVE_ID=0)(axi4_if intf);

  //-------------------------------------------------------
  // Package : Importing Uvm Pakckage and Test Package
  //-------------------------------------------------------
  import uvm_pkg::*;
  `include "uvm_macros.svh"
  
  //-------------------------------------------------------
  // AXI4 Slave Driver bfm instantiation
  //-------------------------------------------------------
  axi4_slave_driver_bfm axi4_slave_drv_bfm_h (.aclk           (intf.aclk)         , 
                                              .aresetn        (intf.aresetn)      ,
                                              .axi_awid_i     (intf.axi_awid)     ,           
                                              .axi_awaddr_i   (intf.axi_awaddr)   ,  
                                              .axi_awlen_i    (intf.axi_awlen)    ,   
                                              .axi_awsize_i   (intf.axi_awsize)   ,  
                                              .axi_awburst_i  (intf.axi_awburst)  , 
                                              .axi_awlock_i   (intf.axi_awlock)   ,  
                                              .axi_awcache_i  (intf.axi_awcache)  , 
                                              .axi_awprot_i   (intf.axi_awprot)   ,  
                                              .axi_awvalid_i  (intf.axi_awvalid)  , 
                                              .axi_awready_o  (intf.axi_awready)  , 
                                                                            
                                              .axi_wid_i      (intf.axi_wid)      ,     
                                              .axi_wdata_i    (intf.axi_wdata)    ,   
                                              .axi_wstrb_i    (intf.axi_wstrb)    ,   
                                              .axi_wlast_i    (intf.axi_wlast)    ,   
                                              .axi_wuser_i    (intf.axi_wuser)    ,   
                                              .axi_wvalid_i   (intf.axi_wvalid)   ,  
                                              .axi_wready_o   (intf.axi_wready)   ,  
                                                              
                                              .axi_bid_o      (intf.axi_bid)      ,    
                                              .axi_bresp_o    (intf.axi_bresp)    ,   
                                              .axi_buser_o    (intf.axi_buser)    ,   
                                              .axi_bvalid_o   (intf.axi_bvalid)   ,  
                                              .axi_bready_i   (intf.axi_bready)   ,  
                                                                            
                                              .axi_arid_i     (intf.axi_arid)     ,    
                                              .axi_araddr_i   (intf.axi_araddr)   ,  
                                              .axi_arlen_i    (intf.axi_arlen)    ,   
                                              .axi_arsize_i   (intf.axi_arsize)   ,  
                                              .axi_arburst_i  (intf.axi_arburst)  , 
                                              .axi_arlock_i   (intf.axi_arlock)   ,  
                                              .axi_arcache_i  (intf.axi_arcache)  , 
                                              .axi_arprot_i   (intf.axi_arprot)   ,  
                                              .axi_arQOS_i    (intf.axi_arQOS)    ,   
                                              .axi_arregion_i (intf.axi_arregion) ,
                                              .axi_aruser_i   (intf.axi_aruser)   ,  
                                              .axi_arvalid_i  (intf.axi_arvalid)  , 
                                              .axi_arready_o  (intf.axi_arready)  , 
                                                                            
                                              .axi_rid_o      (intf.axi_rid)      ,     
                                              .axi_rdata_o    (intf.axi_rdata)    ,   
                                              .axi_rstrb_o    (intf.axi_rstrb)    ,   
                                              .axi_rresp_o    (intf.axi_rresp)    ,   
                                              .axi_rlast_o    (intf.axi_rlast)    ,   
                                              .axi_ruser_o    (intf.axi_ruser)    ,   
                                              .axi_rvalid_o   (intf.axi_rvalid)   ,  
                                              .axi_rready_i   (intf.axi_rready)   
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

  
  initial begin
    `uvm_info("axi4 slave agent bfm",$sformatf("AXI4 SLAVE AGENT BFM"),UVM_LOW);
  end
   
endmodule : axi4_slave_agent_bfm
`endif
