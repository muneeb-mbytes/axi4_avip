`ifndef AXI4_SLAVE_AGENT_BFM_INCLUDED_
`define AXI4_SLAVE_AGENT_BFM_INCLUDED_

//--------------------------------------------------------------------------------------------
// Module:AXI4 Slave Agent BFM
// This module is used as the configuration class for slave agent bfm and its components
//--------------------------------------------------------------------------------------------
module axi4_slave_agent_bfm(axi4_if intf);

  //-------------------------------------------------------
  // Package : Importing Uvm Pakckage and Test Package
  //-------------------------------------------------------
  import uvm_pkg::*;
  `include "uvm_macros.svh"
  
  //-------------------------------------------------------
  // AXI4 Slave Driver bfm instantiation
  //-------------------------------------------------------
  axi4_slave_driver_bfm axi4_slave_drv_bfm_h (.pclk(intf.pclk), 
                                      .aresetn(intf.aresetn)
                                    );
   

  //-------------------------------------------------------
  // AXI4 Slave monitor  bfm instantiation
  //-------------------------------------------------------
  axi4_slave_monitor_bfm axi4_slave_mon_bfm_h (.pclk(intf.pclk), 
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
    $display("AXI4 Slave Agent BFM");
  end
   
endmodule : axi4_slave_agent_bfm
`endif
