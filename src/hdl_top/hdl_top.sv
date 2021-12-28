`ifndef HDL_TOP_INCLUDED_
`define HDL_TOP_INCLUDED_

//--------------------------------------------------------------------------------------------
// Module      : HDL Top
// Description : Has a interface master and slave agent bfm.
//--------------------------------------------------------------------------------------------

module hdl_top;

  //-------------------------------------------------------
  // Clock Reset Initialization
  //-------------------------------------------------------
  bit clk;
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
    clk = 1'b0;
    forever #10 clk = ~clk;
  end

  //-------------------------------------------------------
  // System Reset Generation
  // Active low reset
  //-------------------------------------------------------
  initial begin
    rst = 1'b1;

    repeat (2) begin
      @(posedge clk);
    end
    rst = 1'b0;

    repeat (2) begin
      @(posedge clk);
    end
    rst = 1'b1;
  end
  
  // Variable : intf
  // axi4 Interface Instantiation
  axi4_if intf(.pclk(clk),
              .aresetn(rst));


  // Variable : master_agent_bfm_h
  //axi4 Master BFM Agent Instantiation 
  axi4_master_agent_bfm master_agent_bfm_h(intf); 

  // Variable : slave_agent_bfm_h
  // axi4 Slave BFM Agent Instantiation
  axi4_slave_agent_bfm slave_agent_bfm_h(intf);



endmodule : hdl_top

`endif
