`ifndef AXI4_MASTER_AGENT_BFM_INCLUDED_
`define AXI4_MASTER_AGENT_BFM_INCLUDED_

//--------------------------------------------------------------------------------------------
// Module:AXI4 Master Agent BFM
// This module is used as the configuration class for master agent bfm and its components
//--------------------------------------------------------------------------------------------
module axi4_master_agent_bfm #(parameter int MASTER_ID = 0)(axi4_if intf);

  //-------------------------------------------------------
  // Package : Importing Uvm Pakckage and Test Package
  //-------------------------------------------------------
  import uvm_pkg::*;
  `include "uvm_macros.svh"
  
  //-------------------------------------------------------
  // AXI4 Master Driver bfm instantiation
  //-------------------------------------------------------
  axi4_master_driver_bfm axi4_master_drv_bfm_h (.aclk(intf.aclk), 
                                                .aresetn(intf.aresetn),
                                                .awid(intf.awid),
                                                .awaddr(intf.awaddr),
                                                .awlen(intf.awlen),
                                                .awsize(intf.awsize),
                                                .awburst(intf.awburst),
                                                .awlock(intf.awlock),
                                                .awcache(intf.awcache),
                                                .awprot(intf.awprot),
                                                .awvalid(intf.awvalid),
                                                .awready(intf.awready),
                                                .wdata(intf.wdata),
                                                .wstrb(intf.wstrb),
                                                .wlast(intf.wlast),
                                                .wuser(intf.wuser),
                                                .wvalid(intf.wvalid),
                                                .wready(intf.wready),
                                                .bid(intf.bid),
                                                .bresp(intf.bresp),
                                                .buser(intf.buser),
                                                .bvalid(intf.bvalid),
                                                .bready(intf.bready),
                                                .arid(intf.arid),
                                                .araddr(intf.araddr),
                                                .arlen(intf.arlen),
                                                .arsize(intf.arsize),
                                                .arburst(intf.arburst),
                                                .arlock(intf.arlock),
                                                .arcache(intf.arcache),
                                                .arprot(intf.arprot),
                                                .arQOS(intf.arQOS),
                                                .arregion(intf.arregion),
                                                .aruser(intf.aruser),
                                                .arvalid(intf.arvalid),
                                                .arready(intf.arready),
                                                .rid(intf.rid),
                                                .rdata(intf.rdata),
                                                .rstrb(intf.rstrb),
                                                .rresp(intf.rresp),
                                                .rlast(intf.rlast),
                                                .ruser(intf.ruser),      
                                                .rvalid(intf.rvalid),
                                                .rready(intf.rready)
                                                );
   

  //-------------------------------------------------------
  // AXI4 Master monitor  bfm instantiation
  //-------------------------------------------------------
  axi4_master_monitor_bfm axi4_master_mon_bfm_h (.aclk(intf.aclk),
                                                 .aresetn(intf.aresetn)
                                               );

  //-------------------------------------------------------
  // Setting the virtual handle of BMFs into config_db
  //-------------------------------------------------------
  initial begin
    uvm_config_db#(virtual axi4_master_driver_bfm)::set(null,"*", "axi4_master_driver_bfm", axi4_master_drv_bfm_h); 
    uvm_config_db#(virtual axi4_master_monitor_bfm)::set(null,"*", "axi4_master_monitor_bfm", axi4_master_mon_bfm_h);
  end
  
  //Printing axi4 master agent bfm
  initial begin
    `uvm_info("axi4 master agent bfm",$sformatf("AXI4 MASTER AGENT BFM"),UVM_LOW);
  end
   
endmodule : axi4_master_agent_bfm
`endif
