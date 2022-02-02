`ifndef AXI4_MASTER_COVERAGE_INCLUDED_
`define AXI4_MASTER_COVERAGE_INCLUDED_

//--------------------------------------------------------------------------------------------
// Class: master_coverage
// master_coverage determines the how much code is covered for better functionality of the TB.
//--------------------------------------------------------------------------------------------
class axi4_master_coverage extends uvm_subscriber #(axi4_master_tx);
  `uvm_component_utils(axi4_master_coverage)

  // Variable: axi4_master_agent_cfg_h
  // Declaring handle for master agent configuration class 
  axi4_master_agent_config axi4_master_agent_cfg_h;
 
  //-------------------------------------------------------
  // Covergroup: axi4_master_covergroup
  // Covergroup consists of the various coverpoints based on
  // no. of the variables used to improve the coverage.
  //-------------------------------------------------------
  covergroup axi4_master_covergroup with function sample (axi4_master_agent_config cfg, axi4_master_tx packet);
    option.per_instance = 1;

    //-------------------------------------------------------
    // Write channel signals 
    //-------------------------------------------------------
   
    AWLEN_CP : coverpoint packet.awlen {
      option.comment = "awlen";
      bins AW_LEN[1]={[0:$]}; 
    }

    AWBURST_CP : coverpoint packet.awburst {
      option.comment = "awburst";
      bins READ_FIXED={0};
      bins WRITE_INCR ={1}; 
      bins READ_WRAP={2};     
    }

    AWSIZE_CP : coverpoint packet.awsize {
      option.comment = "awsize";
      bins AWSIZE[]={[0:$]};
    }

    AWLOCK_CP :coverpoint packet.awlock {
      option.comment= "awlock";
      bins AWLOCK_0={0};
      bins AWLOCK_1={1};
    }

    AWCACHE_CP : coverpoint packet.awcache {
      option.comment = "awcache";
      bins AWSIZE[]={[0:$]};
    }

    AWPROT_CP : coverpoint packet.awprot {
      option.comment = "awprot";
      bins AWPROT[]={[0:$]};
    }

    AWID_CP : coverpoint packet.awid {
      option.comment = "awid";
      bins AWID[]={[0:$]};
    }

    BRESP_CP : coverpoint packet.bresp {
      option.comment = "bresp";
      bins BRESP[]={[0:$]};
    }

    //-------------------------------------------------------
    // Read channel signals 
    //-------------------------------------------------------
    
    ARLEN_CP : coverpoint packet.arlen {
      option.comment = "arlen";
      bins AR_LEN[1]={[0:$]}; 
    }

    ARBURST_CP : coverpoint packet.arburst {
      option.comment = "arburst";
      bins READ_FIXED={0};
      bins WRITE_INCR ={1}; 
      bins READ_WRAP={2};     
    }

    ARSIZE_CP : coverpoint packet.arsize {
      option.comment = "arsize";
      bins ARSIZE[]={[0:$]};
    }

    ARLOCK_CP :coverpoint packet.arlock {
      option.comment= "arlock";
      bins ARLOCK_0={0};
      bins ARLOCK_1={1};
    }

    ARCACHE_CP : coverpoint packet.arcache {
      option.comment = "arcache";
      bins ARSIZE[]={[0:$]};
    }

    ARPROT_CP : coverpoint packet.arprot {
      option.comment = "arprot";
      bins ARPROT[]={[0:$]};
    }

    BID_CP : coverpoint packet.bid {
      option.comment = "bid";
      bins BID[]={[0:$]};
    }

    ARID_CP : coverpoint packet.rid {
      option.comment = "arid";
      bins ARID[]={[0:$]};
    }

    RID_CP : coverpoint packet.rid {
      option.comment = "rid";
      bins RID[]={[0:$]};
    }
    
    RRESP_CP : coverpoint packet.rresp {
      option.comment = "rresp";
      bins RRESP[]={[0:$]};
    }
    
    // -------------------------------------------------------------------------------------
    
    TRANSFER_TYPE_CP : coverpoint packet.transfer_type {
      option.comment = "rresp";
      bins TRANSFER_TYPE[]={[0:$]};
    }

    //-------------------------------------------------------
    // Cross of coverpoints
    //-------------------------------------------------------

    AWLENGTH_CP_X_AWSIZE_X_AWBURST    :cross AWLEN_CP,AWSIZE_CP,AWBURST_CP;
    ARLENGTH_CP_X_ARSIZE_X_ARBURST    :cross ARLEN_CP,ARSIZE_CP,ARBURST_CP;
    BID_CP_X_BRESP_CP                 :cross BID_CP,BRESP_CP;
    RID_CP_X_RRESP_CP                 :cross BID_CP,BRESP_CP;
    AWBURST_CP_X_AWLEN_CP_X_AWSIZE_CP :cross AWBURST_CP,AWLEN_CP,AWSIZE_CP;
    ARBURST_CP_X_ARLEN_CP_X_ARSIZE_CP :cross ARBURST_CP,ARLEN_CP,ARSIZE_CP;
    // TRANSFER_TYPE_CP_X_BURST_TYPE_CP  :cross TRANSFER_TYPE_CP,BURST_TYPE_CP;

  endgroup: axi4_master_covergroup


  //-------------------------------------------------------
  // Externally defined Tasks and Functions
  //-------------------------------------------------------
  extern function new(string name = "axi4_master_coverage", uvm_component parent = null);
  extern virtual function void write(axi4_master_tx t);
  extern virtual function void report_phase(uvm_phase phase);

endclass : axi4_master_coverage

//--------------------------------------------------------------------------------------------
// Construct: new
//
// Parameters:
//  name - axi4_master_coverage
//  parent - parent under which this component is created
//--------------------------------------------------------------------------------------------
function axi4_master_coverage::new(string name = "axi4_master_coverage",
                                 uvm_component parent = null);
  super.new(name, parent);
  axi4_master_covergroup =new();
endfunction : new

//--------------------------------------------------------------------------------------------
// Function: write
// sampling is done
//--------------------------------------------------------------------------------------------
function void axi4_master_coverage::write(axi4_master_tx t);
 `uvm_info(get_type_name(),$sformatf("Before calling SAMPLE METHOD"),UVM_HIGH);

  axi4_master_covergroup.sample(axi4_master_agent_cfg_h,t);

  `uvm_info(get_type_name(),"After calling SAMPLE METHOD",UVM_HIGH);
endfunction: write

//--------------------------------------------------------------------------------------------
// Function: report_phase
// Used for reporting the coverage instance percentage values
//--------------------------------------------------------------------------------------------
function void axi4_master_coverage::report_phase(uvm_phase phase);
  `uvm_info(get_type_name(),$sformatf("AXI4 Master Agent Coverage = %0.2f %%", axi4_master_covergroup.get_coverage()), UVM_NONE);
endfunction: report_phase

`endif

