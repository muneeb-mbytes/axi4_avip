`ifndef AXI4_SCOREBOARD_INCLUDED_
`define AXI4_SCOREBOARD_INCLUDED_

//--------------------------------------------------------------------------------------------
// Class: axi4_scoreboard
// Scoreboard the data getting from monitor port that goes into the implementation port
//--------------------------------------------------------------------------------------------
class axi4_scoreboard extends uvm_scoreboard;
  `uvm_component_utils(axi4_scoreboard)

  // Declaring handles for master tx and slave tx
  axi4_master_tx axi4_master_tx_h1;
  axi4_master_tx axi4_master_tx_h2;
  axi4_master_tx axi4_master_tx_h3;
  axi4_master_tx axi4_master_tx_h4;
  axi4_master_tx axi4_master_tx_h5;

  axi4_slave_tx axi4_slave_tx_h1;
  axi4_slave_tx axi4_slave_tx_h2;
  axi4_slave_tx axi4_slave_tx_h3;
  axi4_slave_tx axi4_slave_tx_h4;
  axi4_slave_tx axi4_slave_tx_h5;

  //Variable : axi4_master_analysis_fifo
  //Used to store the axi4_master_data
  uvm_tlm_analysis_fifo#(axi4_master_tx) axi4_master_read_address_analysis_fifo;
  uvm_tlm_analysis_fifo#(axi4_master_tx) axi4_master_read_data_analysis_fifo;
  uvm_tlm_analysis_fifo#(axi4_master_tx) axi4_master_write_address_analysis_fifo;
  uvm_tlm_analysis_fifo#(axi4_master_tx) axi4_master_write_data_analysis_fifo;
  uvm_tlm_analysis_fifo#(axi4_master_tx) axi4_master_write_response_analysis_fifo;
  
  //Variable : axi4_slave_analysis_fifo
  //Used to store the axi4_slave_data
  uvm_tlm_analysis_fifo#(axi4_slave_tx) axi4_slave_read_address_analysis_fifo;
  uvm_tlm_analysis_fifo#(axi4_slave_tx) axi4_slave_read_data_analysis_fifo;
  uvm_tlm_analysis_fifo#(axi4_slave_tx) axi4_slave_write_address_analysis_fifo;
  uvm_tlm_analysis_fifo#(axi4_slave_tx) axi4_slave_write_data_analysis_fifo;
  uvm_tlm_analysis_fifo#(axi4_slave_tx) axi4_slave_write_response_analysis_fifo;

  int byte_data_cmp_verified_awid_count;
  int byte_data_cmp_verified_awaddr_count;
  int byte_data_cmp_verified_awsize_count;
  int byte_data_cmp_verified_awlen_count;
  int byte_data_cmp_verified_awburst_count;
  int byte_data_cmp_verified_awcache_count;
  int byte_data_cmp_verified_awlock_count;
  int byte_data_cmp_verified_awprot_count;

  int byte_data_cmp_verified_wdata_count;
  int byte_data_cmp_verified_wstrb_count;
  int byte_data_cmp_verified_wuser_count;
  //-------------------------------------------------------
  // Externally defined Tasks and Functions
  //-------------------------------------------------------
  extern function new(string name = "axi4_scoreboard", uvm_component parent = null);
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual function void connect_phase(uvm_phase phase);
  extern virtual function void end_of_elaboration_phase(uvm_phase phase);
  extern virtual function void start_of_simulation_phase(uvm_phase phase);
  extern virtual task run_phase(uvm_phase phase);
  extern virtual task axi4_write_address_comparison();
  extern virtual task axi4_write_data_comparison();

endclass : axi4_scoreboard

//--------------------------------------------------------------------------------------------
// Construct: new
//
// Parameters:
//  name - axi4_scoreboard
//  parent - parent under which this component is created
//--------------------------------------------------------------------------------------------
function axi4_scoreboard::new(string name = "axi4_scoreboard",
                                 uvm_component parent = null);
  super.new(name, parent);
  axi4_master_read_address_analysis_fifo = new("axi4_master_read_address_analysis_fifo",this);
  axi4_master_read_data_analysis_fifo = new("axi4_master_read_data_analysis_fifo",this);
  axi4_master_write_address_analysis_fifo = new("axi4_master_write_address_analysis_fifo",this);
  axi4_master_write_data_analysis_fifo = new("axi4_master_write_data_analysis_fifo",this);
  axi4_master_write_response_analysis_fifo= new("axi4_master_write_response_analysis_fifo",this);
 
  axi4_slave_read_address_analysis_fifo = new("axi4_slave_read_address_analysis_fifo",this);
  axi4_slave_read_data_analysis_fifo = new("axi4_slave_read_data_analysis_fifo",this);
  axi4_slave_write_address_analysis_fifo = new("axi4_slave_write_address_analysis_fifo",this);
  axi4_slave_write_data_analysis_fifo = new("axi4_slave_write_data_analysis_fifo",this);
  axi4_slave_write_response_analysis_fifo= new("axi4_slave_write_response_analysis_fifo",this);
endfunction : new

//--------------------------------------------------------------------------------------------
// Function: build_phase
// <Description_here>
//
// Parameters:
//  phase - uvm phase
//--------------------------------------------------------------------------------------------
function void axi4_scoreboard::build_phase(uvm_phase phase);
  super.build_phase(phase);
endfunction : build_phase

//--------------------------------------------------------------------------------------------
// Function: connect_phase
// <Description_here>
//
// Parameters:
//  phase - uvm phase
//--------------------------------------------------------------------------------------------
function void axi4_scoreboard::connect_phase(uvm_phase phase);
  super.connect_phase(phase);
endfunction : connect_phase

//--------------------------------------------------------------------------------------------
// Function: end_of_elaboration_phase
// <Description_here>
//
// Parameters:
//  phase - uvm phase
//--------------------------------------------------------------------------------------------
function void axi4_scoreboard::end_of_elaboration_phase(uvm_phase phase);
  super.end_of_elaboration_phase(phase);
endfunction  : end_of_elaboration_phase

//--------------------------------------------------------------------------------------------
// Function: start_of_simulation_phase
// <Description_here>
//
// Parameters:
//  phase - uvm phase
//--------------------------------------------------------------------------------------------
function void axi4_scoreboard::start_of_simulation_phase(uvm_phase phase);
  super.start_of_simulation_phase(phase);
endfunction : start_of_simulation_phase

//--------------------------------------------------------------------------------------------
// Task: run_phase
// <Description_here>
//
// Parameters:
//  phase - uvm phase
//--------------------------------------------------------------------------------------------
task axi4_scoreboard::run_phase(uvm_phase phase);

  //super.run_phase(phase);

  forever begin
    `uvm_info(get_type_name(),$sformatf("calling analysis fifo in scoreboard"),UVM_HIGH);
    
    axi4_write_address_comparison();
    axi4_write_data_comparison();

    
    axi4_master_write_response_analysis_fifo.get(axi4_master_tx_h3);
    axi4_slave_write_response_analysis_fifo.get(axi4_slave_tx_h3);
    
    axi4_master_read_address_analysis_fifo.get(axi4_master_tx_h4);
    axi4_slave_read_address_analysis_fifo.get(axi4_slave_tx_h4);
    
    axi4_master_read_data_analysis_fifo.get(axi4_master_tx_h5);
    axi4_slave_read_data_analysis_fifo.get(axi4_slave_tx_h5);

    //-------------------------------------------------------
    // Printing data from all fifo's
    //-------------------------------------------------------

    // `uvm_info(get_type_name(),$sformatf("checking fifo used is %d",axi4_master_write_address_analysis_fifo.used()),UVM_HIGH)
    `uvm_info(get_type_name(),$sformatf("scoreboard's axi4_master_write_data \n%s",axi4_master_tx_h2.sprint()),UVM_HIGH)
    `uvm_info(get_type_name(),$sformatf("scoreboard's axi4_master_write_response \n%s",axi4_master_tx_h3.sprint()),UVM_HIGH)
    `uvm_info(get_type_name(),$sformatf("scoreboard's axi4_master_read_address \n%s",axi4_master_tx_h4.sprint()),UVM_HIGH)
    `uvm_info(get_type_name(),$sformatf("scoreboard's axi4_master_read_data \n%s",axi4_master_tx_h5.sprint()),UVM_HIGH)
    `uvm_info(get_type_name(),$sformatf("after printing all fifo's data in scoreboard"),UVM_HIGH);
    `uvm_info(get_type_name(),$sformatf("scoreboard's axi4_slave_write_address \n%s",axi4_slave_tx_h1.sprint()),UVM_HIGH)
    `uvm_info(get_type_name(),$sformatf("scoreboard's axi4_slave_write_data \n%s",axi4_slave_tx_h2.sprint()),UVM_HIGH)
    `uvm_info(get_type_name(),$sformatf("scoreboard's axi4_slave_write_response \n%s",axi4_slave_tx_h3.sprint()),UVM_HIGH)
    `uvm_info(get_type_name(),$sformatf("scoreboard's axi4_slave_read_address \n%s",axi4_slave_tx_h4.sprint()),UVM_HIGH)
    `uvm_info(get_type_name(),$sformatf("scoreboard's axi4_slave_read_data \n%s",axi4_slave_tx_h5.sprint()),UVM_HIGH)

    // Checking data for address in both master and slave
    foreach(axi4_master_tx_h1.awaddr[i])
    if(axi4_master_tx_h1.awaddr[i]!=axi4_slave_tx_h1.awaddr[i])
    begin
       `uvm_error("Scoreboard awaddr mismatch",$sformatf("awaddr[%0d] = %0h",i,axi4_master_tx_h1.awaddr[i]));;
    end
    else
    begin
      `uvm_info (get_type_name(), $sformatf ("scoreboard awaddr matched"),UVM_HIGH);
    end

    `uvm_info(get_type_name(),$sformatf("scoreboard's axi4_slave_write_data \n%s",axi4_slave_tx_h2.sprint()),UVM_HIGH)
    `uvm_info(get_type_name(),$sformatf("scoreboard's axi4_slave_write_response \n%s",axi4_slave_tx_h3.sprint()),UVM_HIGH)
    `uvm_info(get_type_name(),$sformatf("scoreboard's axi4_slave_read_address \n%s",axi4_slave_tx_h4.sprint()),UVM_HIGH)
    `uvm_info(get_type_name(),$sformatf("scoreboard's axi4_slave_read_data \n%s",axi4_slave_tx_h5.sprint()),UVM_HIGH)
  end
endtask : run_phase

task axi4_scoreboard::axi4_write_address_comparison();

    axi4_master_write_address_analysis_fifo.get(axi4_master_tx_h1);
    `uvm_info(get_type_name(),$sformatf("scoreboard's axi4_master_write_address_channel \n%s",axi4_master_tx_h1.sprint()),UVM_HIGH)
    axi4_slave_write_address_analysis_fifo.get(axi4_slave_tx_h1);
    `uvm_info(get_type_name(),$sformatf("scoreboard's axi4_slave_write_address_channel \n%s",axi4_slave_tx_h1.sprint()),UVM_HIGH)
    
    //$display("---------------------------------------------------------------------------------");
    //$display("SCOREBOARD WRITE ADDRESS CHANNEL COMPARISIONS");
    //$display("---------------------------------------------------------------------------------");
    if(axi4_master_tx_h1.awid == axi4_slave_tx_h1.awid)begin
      `uvm_info(get_type_name(),$sformatf("axi4_awid from master and slave is equal"),UVM_HIGH);
      `uvm_info("SB_AWID_MATCHED", $sformatf("Master AWID = 'h%0x and Slave AWID = 'h%0x",axi4_master_tx_h1.awid,axi4_slave_tx_h1.awid), UVM_HIGH);             
      byte_data_cmp_verified_awid_count++;
    end
    else begin
      `uvm_info(get_type_name(),$sformatf("axi4_awid from master and slave is  not equal"),UVM_HIGH);
      `uvm_info("SB_AWID_NOT_MATCHED", $sformatf("Master AWID = 'h%0x and Slave AWID = 'h%0x",axi4_master_tx_h1.awid,axi4_slave_tx_h1.awid), UVM_HIGH);             
    end
  
    if(axi4_master_tx_h1.awaddr == axi4_slave_tx_h1.awaddr)begin
      `uvm_info(get_type_name(),$sformatf("axi4_awaddr from master and slave is equal"),UVM_HIGH);
      `uvm_info("SB_AWADDR_MATCHED", $sformatf("Master AWADDR = 'h%0x and Slave AWADDR = 'h%0x",axi4_master_tx_h1.awaddr,axi4_slave_tx_h1.awaddr), UVM_HIGH);             
      byte_data_cmp_verified_awaddr_count++;
    end
    else begin
      `uvm_info(get_type_name(),$sformatf("axi4_awaddr from master and slave is  not equal"),UVM_HIGH);
      `uvm_info("SB_AWADDR_NOT_MATCHED", $sformatf("Master AWADDR = 'h%0x and Slave AWADDR = 'h%0x",axi4_master_tx_h1.awaddr,axi4_slave_tx_h1.awaddr), UVM_HIGH);             
    end

    if(axi4_master_tx_h1.awlen == axi4_slave_tx_h1.awlen)begin
      `uvm_info(get_type_name(),$sformatf("axi4_awlen from master and slave is equal"),UVM_HIGH);
      `uvm_info("SB_awlen_MATCHED", $sformatf("Master awlen = 'h%0x and Slave awlen = 'h%0x",axi4_master_tx_h1.awlen,axi4_slave_tx_h1.awlen), UVM_HIGH);             
      byte_data_cmp_verified_awlen_count++;
    end
    else begin
      `uvm_info(get_type_name(),$sformatf("axi4_awlen from master and slave is  not equal"),UVM_HIGH);
      `uvm_info("SB_awlen_NOT_MATCHED", $sformatf("Master awlen = 'h%0x and Slave awlen = 'h%0x",axi4_master_tx_h1.awlen,axi4_slave_tx_h1.awlen), UVM_HIGH);             
    end

    if(axi4_master_tx_h1.awsize == axi4_slave_tx_h1.awsize)begin
      `uvm_info(get_type_name(),$sformatf("axi4_awsize from master and slave is equal"),UVM_HIGH);
      `uvm_info("SB_awsize_MATCHED", $sformatf("Master awsize = 'h%0x and Slave awsize = 'h%0x",axi4_master_tx_h1.awsize,axi4_slave_tx_h1.awsize), UVM_HIGH);             
      byte_data_cmp_verified_awsize_count++;
    end
    else begin
      `uvm_info(get_type_name(),$sformatf("axi4_awsize from master and slave is  not equal"),UVM_HIGH);
      `uvm_info("SB_awsize_NOT_MATCHED", $sformatf("Master awsize = 'h%0x and Slave awsize = 'h%0x",axi4_master_tx_h1.awsize,axi4_slave_tx_h1.awsize), UVM_HIGH);             
    end

    if(axi4_master_tx_h1.awburst == axi4_slave_tx_h1.awburst)begin
      `uvm_info(get_type_name(),$sformatf("axi4_awburst from master and slave is equal"),UVM_HIGH);
      `uvm_info("SB_awburst_MATCHED", $sformatf("Master awburst = 'h%0x and Slave awburst = 'h%0x",axi4_master_tx_h1.awburst,axi4_slave_tx_h1.awburst), UVM_HIGH);             
      byte_data_cmp_verified_awburst_count++;
    end
    else begin
      `uvm_info(get_type_name(),$sformatf("axi4_awburst from master and slave is  not equal"),UVM_HIGH);
      `uvm_info("SB_awburst_NOT_MATCHED", $sformatf("Master awburst = 'h%0x and Slave awburst = 'h%0x",axi4_master_tx_h1.awburst,axi4_slave_tx_h1.awburst), UVM_HIGH);             
    end

    if(axi4_master_tx_h1.awlock == axi4_slave_tx_h1.awlock)begin
      `uvm_info(get_type_name(),$sformatf("axi4_awlock from master and slave is equal"),UVM_HIGH);
      `uvm_info("SB_awlock_MATCHED", $sformatf("Master awlock = 'h%0x and Slave awlock = 'h%0x",axi4_master_tx_h1.awlock,axi4_slave_tx_h1.awlock), UVM_HIGH);             
      byte_data_cmp_verified_awlock_count++;
    end
    else begin
      `uvm_info(get_type_name(),$sformatf("axi4_awlock from master and slave is  not equal"),UVM_HIGH);
      `uvm_info("SB_awlock_NOT_MATCHED", $sformatf("Master awlock = 'h%0x and Slave awlock = 'h%0x",axi4_master_tx_h1.awlock,axi4_slave_tx_h1.awlock), UVM_HIGH);             
    end

    if(axi4_master_tx_h1.awcache == axi4_slave_tx_h1.awcache)begin
      `uvm_info(get_type_name(),$sformatf("axi4_awcache from master and slave is equal"),UVM_HIGH);
      `uvm_info("SB_awcache_MATCHED", $sformatf("Master awcache = 'h%0x and Slave awcache = 'h%0x",axi4_master_tx_h1.awcache,axi4_slave_tx_h1.awcache), UVM_HIGH);             
      byte_data_cmp_verified_awcache_count++;
    end
    else begin
      `uvm_info(get_type_name(),$sformatf("axi4_awcache from master and slave is  not equal"),UVM_HIGH);
      `uvm_info("SB_awcache_NOT_MATCHED", $sformatf("Master awcache = 'h%0x and Slave awcache = 'h%0x",axi4_master_tx_h1.awcache,axi4_slave_tx_h1.awcache), UVM_HIGH);             
    end

    if(axi4_master_tx_h1.awprot == axi4_slave_tx_h1.awprot)begin
      `uvm_info(get_type_name(),$sformatf("axi4_awprot from master and slave is equal"),UVM_HIGH);
      `uvm_info("SB_awprot_MATCHED", $sformatf("Master awprot = 'h%0x and Slave awprot = 'h%0x",axi4_master_tx_h1.awprot,axi4_slave_tx_h1.awprot), UVM_HIGH);             
      byte_data_cmp_verified_awprot_count++;
    end
    else begin
      `uvm_info(get_type_name(),$sformatf("axi4_awprot from master and slave is  not equal"),UVM_HIGH);
      `uvm_info("SB_awprot_NOT_MATCHED", $sformatf("Master awprot = 'h%0x and Slave awprot = 'h%0x",axi4_master_tx_h1.awprot,axi4_slave_tx_h1.awprot), UVM_HIGH);             
    end

endtask : axi4_write_address_comparison

//-------------------------------------------------------
// Task : axi4_write_data_comparison
//-------------------------------------------------------
task axi4_scoreboard::axi4_write_data_comparison();

    axi4_master_write_data_analysis_fifo.get(axi4_master_tx_h2);
    `uvm_info(get_type_name(),$sformatf("scoreboard's axi4_master_write_data_channel \n%s",axi4_master_tx_h2.sprint()),UVM_HIGH)
    axi4_slave_write_data_analysis_fifo.get(axi4_slave_tx_h2);
    `uvm_info(get_type_name(),$sformatf("scoreboard's axi4_slave_write_data_channel \n%s",axi4_slave_tx_h2.sprint()),UVM_HIGH)
    //$display("---------------------------------------------------------------------------------");
    //$display("SCOREBOARD WRITE DATA CHANNEL COMPARISIONS");
    //$display("---------------------------------------------------------------------------------");
  
    if(axi4_master_tx_h2.wdata == axi4_slave_tx_h2.wdata)begin
      `uvm_info(get_type_name(),$sformatf("axi4_wdata from master and slave is equal"),UVM_HIGH);
      `uvm_info("SB_wdata_MATCHED", $sformatf("Master wdata = %0p and Slave wdata = %0p",axi4_master_tx_h2.wdata,axi4_slave_tx_h2.wdata), UVM_HIGH);             
      byte_data_cmp_verified_wdata_count++;
    end
    else begin
      `uvm_info(get_type_name(),$sformatf("axi4_wdata from master and slave is  not equal"),UVM_HIGH);
      `uvm_info("SB_wdata_NOT_MATCHED", $sformatf("Master wdata = %0p and Slave wdata = %0p",axi4_master_tx_h2.wdata,axi4_slave_tx_h2.wdata), UVM_HIGH);             
    end

    if(axi4_master_tx_h2.wstrb == axi4_slave_tx_h2.wstrb)begin
      `uvm_info(get_type_name(),$sformatf("axi4_wstrb from master and slave is equal"),UVM_HIGH);
      `uvm_info("SB_wstrb_MATCHED", $sformatf("Master wstrb = %0p and Slave wstrb = %0p",axi4_master_tx_h2.wstrb,axi4_slave_tx_h2.wstrb), UVM_HIGH);             
      byte_data_cmp_verified_wstrb_count++;
    end
    else begin
      `uvm_info(get_type_name(),$sformatf("axi4_wstrb from master and slave is  not equal"),UVM_HIGH);
      `uvm_info("SB_wstrb_NOT_MATCHED", $sformatf("Master wstrb = %0p and Slave wstrb = %0p",axi4_master_tx_h2.wstrb,axi4_slave_tx_h2.wstrb), UVM_HIGH);             
    end

    if(axi4_master_tx_h2.wuser == axi4_slave_tx_h2.wuser)begin
      `uvm_info(get_type_name(),$sformatf("axi4_wuser from master and slave is equal"),UVM_HIGH);
      `uvm_info("SB_wuser_MATCHED", $sformatf("Master wuser = 'h%0x and Slave wuser = 'h%0x",axi4_master_tx_h2.wuser,axi4_slave_tx_h2.wuser), UVM_HIGH);             
      byte_data_cmp_verified_wuser_count++;
    end
    else begin
      `uvm_info(get_type_name(),$sformatf("axi4_wuser from master and slave is  not equal"),UVM_HIGH);
      `uvm_info("SB_wuser_NOT_MATCHED", $sformatf("Master wuser = 'h%0x and Slave wuser = 'h%0x",axi4_master_tx_h2.wuser,axi4_slave_tx_h2.wuser), UVM_HIGH);             
    end


endtask : axi4_write_data_comparison

`endif


