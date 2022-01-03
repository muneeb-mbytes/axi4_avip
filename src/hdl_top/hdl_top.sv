`ifndef HDL_TOP_INCLUDED_
`define HDL_TOP_INCLUDED_

//--------------------------------------------------------------------------------------------
// Module      : HDL Top
// Description : Has a interface master and slave agent bfm.
//--------------------------------------------------------------------------------------------

module hdl_top;

  import uvm_pkg::*;
  import axi4_globals_pkg::*;
  `include "uvm_macros.svh"

  //-------------------------------------------------------
  // Clock Reset Initialization
  //-------------------------------------------------------
  bit aclk;
  bit rst;

  //-------------------------------------------------------
  // Display statement for HDL_TOP
  //-------------------------------------------------------
  initial begin
    $display("HDL_TOP");
  end

  //-------------------------------------------------------
  // System Clock Generation
  //-------------------------------------------------------
  initial begin
    aclk = 1'b0;
    forever #10 aclk = ~aclk;
  end

  //-------------------------------------------------------
  // System Reset Generation
  // Active low reset
  //-------------------------------------------------------
  initial begin
    rst = 1'b1;

    repeat (2) begin
      @(posedge aclk);
    end
    rst = 1'b0;

    repeat (2) begin
      @(posedge aclk);
    end
    rst = 1'b1;
  end
  
  // Variable : intf
  // axi4 Interface Instantiation
  axi4_if intf(.aclk(aclk),
              .aresetn(rst));

  //-------------------------------------------------------
  // axi4 master BFM Agent Instantiation
  //-------------------------------------------------------
//  genvar i;
//  generate
//    for (i=0; i < NO_OF_MASTERS ; i++) begin : apb_master_agent_bfm
//      axi4_master_agent_bfm #(.MASTER_ID(i)) axi4_mster_agent_bfm_h(intf);
//      //defparam axi4_master_agent_bfm[i].axi4_master_agent_bfm_h.MASTER_ID = i;
//    end
//  endgenerate
//  
//  //-------------------------------------------------------
//  // axi4 slave BFM Agent Instantiation
//  //-------------------------------------------------------
//  genvar j;
//  generate
//    for (j=0; j < NO_OF_SLAVES; j++) begin : apb_slave_agent_bfm
//      axi4_slave_agent_bfm #(.SLAVE_ID(j)) axi4_slave_agent_bfm_h(intf);
//      //defparam axi4_slave_agent_bfm[j].axi4_slave_agent_bfm_h.SLAVE_ID = j;
//    end
//  endgenerate
  

//<<<<<<< HEAD
  // Variable : master_agent_bfm_h
  //axi4 Master BFM Agent Instantiation 
  //axi4_master_agent_bfm master_agent_bfm_h(intf); 

  // Variable : slave_agent_bfm_h
  // axi4 Slave BFM Agent Instantiation
  //axi4_slave_agent_bfm slave_agent_bfm_h(intf);

//=======
//  // Variable : master_agent_bfm_h
//  //axi4 Master BFM Agent Instantiation 
//  axi4_master_agent_bfm master_agent_bfm_h(intf); 
//
//  // Variable : slave_agent_bfm_h
//  // axi4 Slave BFM Agent Instantiation
//  axi4_slave_agent_bfm slave_agent_bfm_h(intf);
//>>>>>>> 3f5e56cecb0a64d037433ebd7887cfda85dd2647

  //-------------------------------------------------------
  // AXI4  No of Master and Slaves Agent Instantiation
  //-------------------------------------------------------
  genvar i;
  generate
    for (i=0; i < NO_OF_MASTERS; i++) begin : axi4_master_agent_bfm
      axi4_master_agent_bfm #(.MASTER_ID(i)) axi4_master_agent_bfm_h(intf);
      defparam axi4_master_agent_bfm[i].axi4_master_agent_bfm_h.MASTER_ID = i;
    end
    for (i=0; i < NO_OF_SLAVES; i++) begin : axi4_slave_agent_bfm
      axi4_slave_agent_bfm #(.SLAVE_ID(i)) axi4_slave_agent_bfm_h(intf);
      defparam axi4_slave_agent_bfm[i].axi4_slave_agent_bfm_h.SLAVE_ID = i;
    end
  endgenerate

  
endmodule : hdl_top

`endif
