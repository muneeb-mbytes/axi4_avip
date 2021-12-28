`ifndef AXI4_SLAVE_DRIVER_BFM_INCLUDED_
`define AXI4_SLAVE_DRIVER_BFM_INCLUDED_

//--------------------------------------------------------------------------------------------
//Interface : axi4_slave_driver_bfm
//Used as the HDL driver for axi4
//It connects with the HVL driver_proxy for driving the stimulus
//--------------------------------------------------------------------------------------------
import axi4_globals_pkg::*;
interface axi4_slave_driver_bfm(input pclk, input aresetn); 
  //-------------------------------------------------------
  // Importing UVM Package 
  //-------------------------------------------------------
  import uvm_pkg::*;
  `include "uvm_macros.svh" 
  //-------------------------------------------------------
  // Importing axi4 Global Package slave package
  //-------------------------------------------------------
  import axi4_slave_pkg::axi4_slave_driver_proxy;

  //--------------------------------------------------------------------------------------------
  // Creating handle for virtual Interface
  //--------------------------------------------------------------------------------------------
 
  //Variable : axi4_slave_driver_proxy_h
  //Creating the handle for proxy driver
  axi4_slave_driver_proxy axi4_slave_drv_proxy_h;

  initial begin
    $display("AXI Slave driver BFM");
  end

endinterface : axi4_slave_driver_bfm
`endif
