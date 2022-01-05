`ifndef AXI4_MASTER_DRIVER_BFM_INCLUDED_
`define AXI4_MASTER_DRIVER_BFM_INCLUDED_

//--------------------------------------------------------------------------------------------
//Interface : axi4_master_driver_bfm
//Used as the HDL driver for axi4
//It connects with the HVL driver_proxy for driving the stimulus
//--------------------------------------------------------------------------------------------
import axi4_globals_pkg::*;
interface axi4_master_driver_bfm(input aclk, input aresetn); 
  //-------------------------------------------------------
  // Importing UVM Package 
  //-------------------------------------------------------
  import uvm_pkg::*;
  `include "uvm_macros.svh" 
  //-------------------------------------------------------
  // Importing axi4 Global Package master package
  //-------------------------------------------------------
  import axi4_master_pkg::axi4_master_driver_proxy;

  //--------------------------------------------------------------------------------------------
  // Creating handle for virtual Interface
  //--------------------------------------------------------------------------------------------
 
  //Variable : axi4_master_driver_proxy_h
  //Creating the handle for proxy driver
  axi4_master_driver_proxy axi4_master_drv_proxy_h;

  initial begin
    `uvm_info("axi4 master driver bfm",$sformatf("AXI4 MASTER DRIVER BFM"),UVM_LOW);
  end

endinterface : axi4_master_driver_bfm
`endif
