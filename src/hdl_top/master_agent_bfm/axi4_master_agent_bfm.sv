`ifndef AXI4_MASTER_AGENT_BFM_INCLUDED_
`define AXI4_MASTER_AGENT_BFM_INCLUDED_

//--------------------------------------------------------------------------------------------
// Module:AXI4 Master Agent BFM
// This module is used as the configuration class for master agent bfm and its components
//--------------------------------------------------------------------------------------------
module axi4_master_agent_bfm(axi4_if intf);

  //-------------------------------------------------------
  // Package : Importing Uvm Pakckage and Test Package
  //-------------------------------------------------------
  import uvm_pkg::*;
  `include "uvm_macros.svh"
  
  //-------------------------------------------------------
  // AXI4 Master Driver bfm instantiation
  //-------------------------------------------------------
  axi4_master_driver_bfm axi4_master_drv_bfm_h (.pclk(intf.pclk), 
                                      .aresetn(intf.aresetn)
                                    );
   

  //-------------------------------------------------------
  // AXI4 Master monitor  bfm instantiation
  //-------------------------------------------------------
  axi4_master_monitor_bfm axi4_master_mon_bfm_h (.pclk(intf.pclk), 
                                       .aresetn(intf.aresetn)
                                     );

  //-------------------------------------------------------
  // Setting the virtual handle of BMFs into config_db
  //-------------------------------------------------------
  initial begin
    uvm_config_db#(virtual axi4_master_driver_bfm)::set(null,"*", "axi4_master_driver_bfm", axi4_master_drv_bfm_h); 
    uvm_config_db#(virtual axi4_master_monitor_bfm)::set(null,"*", "axi4_master_monitor_bfm", axi4_master_mon_bfm_h);
  end

  
  initial begin
    $display("AXI4 Master Agent BFM");
  end
   
endmodule : axi4_master_agent_bfm
`endif
