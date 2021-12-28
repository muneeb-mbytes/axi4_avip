`ifndef AXI4_SLAVE_MONITOR_BFM_INCLUDED_
`define AXI4_SLAVE_MONITOR_BFM_INCLUDED_

//--------------------------------------------------------------------------------------------
//Interface : axi4_slave_monitor_bfm
//Used as the HDL monitor for axi4
//It connects with the HVL monitor_proxy for driving the stimulus
//--------------------------------------------------------------------------------------------
import axi4_globals_pkg::*;
interface axi4_slave_monitor_bfm(input pclk, input aresetn); 
  //-------------------------------------------------------
  // Importing UVM Package 
  //-------------------------------------------------------
  import uvm_pkg::*;
  `include "uvm_macros.svh" 
  //-------------------------------------------------------
  // Importing axi4 Global Package slave package
  //-------------------------------------------------------
  import axi4_slave_pkg::axi4_slave_monitor_proxy;

  //--------------------------------------------------------------------------------------------
  // Creating handle for virtual Interface
  //--------------------------------------------------------------------------------------------
 
  //Variable : axi4_slave_monitor_proxy_h
  //Creating the handle for proxy monitor
  axi4_slave_monitor_proxy axi4_slave_mon_proxy_h;

  initial begin
    $display("AXI Slave Monitor BFM");
  end

endinterface : axi4_slave_monitor_bfm
`endif
