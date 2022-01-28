`ifndef AXI4_SLAVE_COVERAGE_INCLUDED_
`define AXI4_SLAVE_COVERAGE_INCLUDED_

//--------------------------------------------------------------------------------------------
// Class: slave_coverage
// slave_coverage determines the how much code is covered for better functionality of the TB.
//--------------------------------------------------------------------------------------------
class axi4_slave_coverage extends uvm_subscriber#(axi4_slave_tx);
  `uvm_component_utils(axi4_slave_coverage)

  // Variable: axi4_slave_agent_cfg_h;
  // Handle for axi4_slave agent configuration
  axi4_slave_agent_config axi4_slave_agent_cfg_h;

  //-------------------------------------------------------
  // Covergroup: axi4_slave_covergroup
  // Covergroup consists of the various coverpoints based on
  // no. of the variables used to improve the coverage.
  //-------------------------------------------------------
  covergroup axi4_slave_covergroup with function sample (axi4_slave_agent_config cfg, axi4_slave_tx packet);
    option.per_instance = 1;

    AWLEN_CP : coverpoint packet.awlen {
      option.comment = "awlen";
      bins AW_LEN[16]={[0:$]}; 
    }

    AWBURST_CP : coverpoint packet.awburst {
      option.comment = "awburst";
      bins AWBURST[]={[0:$]};
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

// --------------------------------------------------------------------------

    ARBURST_CP : coverpoint packet.arburst {
      option.comment = "arburst";
      bins ARBURST[]={[0:$]};
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

  endgroup: axi4_slave_covergroup

  //-------------------------------------------------------
  // Externally defined Tasks and Functions
  //-------------------------------------------------------
  extern function new(string name = "axi4_slave_coverage", uvm_component parent = null);
  extern virtual function void write(axi4_slave_tx t);
  extern virtual function void report_phase(uvm_phase phase);
endclass : axi4_slave_coverage

//--------------------------------------------------------------------------------------------
// Construct: new
//
// Parameters:
//  name - axi4_slave_coverage
//  parent - parent under which this component is created
//--------------------------------------------------------------------------------------------
function axi4_slave_coverage::new(string name = "axi4_slave_coverage",uvm_component parent = null);
  super.new(name, parent);
  axi4_slave_covergroup =new();
  
endfunction : new

//--------------------------------------------------------------------------------------------
// Function: write
// sampiling is done
//--------------------------------------------------------------------------------------------
function void axi4_slave_coverage::write(axi4_slave_tx t);
 `uvm_info(get_type_name(),$sformatf("Before calling SAMPLE METHOD"),UVM_HIGH);

  axi4_slave_covergroup.sample(axi4_slave_agent_cfg_h,t);

  `uvm_info(get_type_name(),"After calling SAMPLE METHOD",UVM_HIGH);

endfunction: write

//--------------------------------------------------------------------------------------------
// Function: report_phase
// Used for reporting the coverage instance percentage values
//--------------------------------------------------------------------------------------------
function void axi4_slave_coverage::report_phase(uvm_phase phase);
  `uvm_info(get_type_name(),$sformatf("AXI4 Slave Agent Coverage = %0.2f %%", axi4_slave_covergroup.get_coverage()), UVM_NONE);
endfunction: report_phase

`endif

