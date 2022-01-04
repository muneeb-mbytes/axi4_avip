`ifndef AXI4_MASTER_TX_INCLUDED_
`define AXI4_MASTER_TX_INCLUDED_

//--------------------------------------------------------------------------------------------
// Class: axi4_master_tx
// This class holds the data items required to drive the stimulus to dut
// and also holds methods that manipulate those data items.
//--------------------------------------------------------------------------------------------
class axi4_master_tx extends uvm_sequence_item;
  
  `uvm_object_utils(axi4_master_tx)

  //Variable : awid
  //Used to send the write address id
  rand awid_e awid;

  //Variable : awaddr
  //Used to send the write address
  rand bit[ADDRESS_WIDTH-1:0]awaddr;

  //Variable : awlen
  //Used to send the write address length
  rand awlen_e awlen;

  //Variable : awsize
  //Used to send the write address size
  rand awsize_e awsize;
  
  //Variable : awburst
  //Used to send the write address burst
  rand awburst_e awburst;

  //Variable : awlock
  //Used to send the write address lock
  rand awlock_e awlock;
  
  //Variable : awcache
  //Used to send the write address cache
  rand awcache_e awcache;

  //Variable : awprot
  //Used to send the write address prot
  rand awprot_e awprot;

  //Variable : awqos
  //Used to send the write address quality of service
  rand bit awqos;

  //Variable : awvalid
  //Used to send the write address valid
  //bit awvalid;
  
  //Variable : awready
  //Used to send the write address ready
  //bit awready;

  //Variable : wdata
  //Used to randomise write data
  rand bit[DATA_WIDTH-1:0]wdata;

  //Variable : wstrb
  //Used to randomise write strobe
  rand bit[DATA_WIDTH/8-1:0]wstrb;

  //Variable : wlast
  //Used to store the write last transfer
  //bit wlast;

  //Variable : wvalid
  //Used to send the write valid
  //bit wvalid;
  
  //Variable : wready
  //Used to send the write ready
  //bit wready;

  //Variable : bid
  //Used to send the response id
  bid_e bid;

  //Variable : bresp
  //Used to capture the write response of the trasnaction
  bresp_e bresp;

  //Variable : arid
  //Used to send the read address id
  rand arid_e arid;

  //Variable : araddr
  //Used to send the read address
  rand bit[ADDRESS_WIDTH-1:0]araddr;

  //Variable : arlen
  //Used to send the read address length
  rand arlen_e arlen;

  //Variable : arsize
  //Used to send the read address size
  rand arsize_e arsize;
  
  //Variable : arburst
  //Used to send the read address burst
  rand arburst_e arburst;

  //Variable : arlock
  //Used to send the read address lock
  rand arlock_e arlock;
  
  //Variable : arcache
  //Used to send the read address cache
  rand arcache_e arcache;

  //Variable : arprot
  //Used to send the read address prot
  rand arprot_e arprot;

  //Variable : arqos
  //Used to send the read address quality of service
  rand bit arqos;

  //Variable : arvalid
  //Used to send the read address valid
  //bit arvalid;

  //Variable : arready
  //Used to send the read address ready
  //bit arready;

  //Variable : rdata
  //Used to randomise read data
  rand bit[DATA_WIDTH-1:0]rdata;

  //Variable : rstrb
  //Used to randomise read strobe
  rand bit[DATA_WIDTH/8-1:0]rstrb;

  //Variable : rresp
  //Used to capture the read response of the trasnaction
  rresp_e rresp;

  //Variable : rlast
  //Used to store the read last transfer
  //bit rlast;

  //Variable : rvalid
  //Used to send the read valid
  //bit rvalid;
  
  //Variable : rready
  //Used to send the read ready
  //bit rready;

  //-------------------------------------------------------
  // Externally defined Tasks and Functions
  //-------------------------------------------------------
  extern function new(string name = "axi4_master_tx");
  extern function void do_copy(uvm_object rhs);
  extern function bit do_compare(uvm_object rhs, uvm_comparer comparer);
  extern function void do_print(uvm_printer printer);
endclass : axi4_master_tx

//--------------------------------------------------------------------------------------------
//  Construct: new
//  initializes the class object
//
//  Parameters:
//  name - axi4_master_tx
//--------------------------------------------------------------------------------------------
function axi4_master_tx::new(string name = "axi4_master_tx");
  super.new(name);
endfunction : new

//--------------------------------------------------------------------------------------------
// Function : do_copy
// Copies the axi4 slave_tx into the rhs object
//
// Parameters:
// rhs  - uvm_object
//--------------------------------------------------------------------------------------------
function void axi4_master_tx::do_copy(uvm_object rhs);
  axi4_master_tx axi4_master_tx_copy_obj;

  if(!$cast(axi4_master_tx_copy_obj,rhs)) begin
    `uvm_fatal("do_copy","cast of the rhs object failed")
  end
  super.do_copy(rhs);

  awid    = axi4_master_tx_copy_obj.awid;
  awaddr  = axi4_master_tx_copy_obj.awaddr;
  awlen   = axi4_master_tx_copy_obj.awlen;
  awsize  = axi4_master_tx_copy_obj.awsize;
  awburst = axi4_master_tx_copy_obj.awburst;
  awlock  = axi4_master_tx_copy_obj.awlock;
  awcache = axi4_master_tx_copy_obj.awcache;
  awprot  = axi4_master_tx_copy_obj.awprot;
  awqos   = axi4_master_tx_copy_obj.awqos;
  wdata   = axi4_master_tx_copy_obj.wdata;
  wstrb   = axi4_master_tx_copy_obj.wstrb;
  bid     = axi4_master_tx_copy_obj.bid;
  bresp   = axi4_master_tx_copy_obj.bresp;
  arid    = axi4_master_tx_copy_obj.arid;
  araddr  = axi4_master_tx_copy_obj.araddr;
  arlen   = axi4_master_tx_copy_obj.arlen;
  arsize  = axi4_master_tx_copy_obj.arsize;
  arburst = axi4_master_tx_copy_obj.arburst;
  arlock  = axi4_master_tx_copy_obj.arlock;
  arcache = axi4_master_tx_copy_obj.arcache;
  arprot  = axi4_master_tx_copy_obj.arprot;
  arqos   = axi4_master_tx_copy_obj.arqos;
  rdata   = axi4_master_tx_copy_obj.rdata;
  rstrb   = axi4_master_tx_copy_obj.rstrb;
  rresp   = axi4_master_tx_copy_obj.rresp;
  
endfunction : do_copy

//--------------------------------------------------------------------------------------------
// Function: do_compare
// Compare method is implemented using handle rhs
//
// Parameters:
// phase - uvm phase
//--------------------------------------------------------------------------------------------
function bit axi4_master_tx::do_compare (uvm_object rhs, uvm_comparer comparer);
  axi4_master_tx axi4_master_tx_compare_obj;

  if(!$cast(axi4_master_tx_compare_obj,rhs)) begin
    `uvm_fatal("FATAL_axi_MASTER_TX_DO_COMPARE_FAILED","cast of the rhs object failed")
    return 0;
  end
  
  return super.do_compare(axi4_master_tx_compare_obj, comparer) &&
  awid    == axi4_master_tx_compare_obj.awid    &&
  awaddr  == axi4_master_tx_compare_obj.awaddr  &&
  awlen   == axi4_master_tx_compare_obj.awlen   &&
  awsize  == axi4_master_tx_compare_obj.awsize  &&
  awburst == axi4_master_tx_compare_obj.awburst &&
  awlock  == axi4_master_tx_compare_obj.awlock  &&
  awcache == axi4_master_tx_compare_obj.awcache &&
  awprot  == axi4_master_tx_compare_obj.awprot  &&
  awqos   == axi4_master_tx_compare_obj.awqos   &&
  wdata   == axi4_master_tx_compare_obj.wdata   &&
  wstrb   == axi4_master_tx_compare_obj.wstrb   &&
  bid     == axi4_master_tx_compare_obj.bid     &&
  bresp   == axi4_master_tx_compare_obj.bresp   &&
  arid    == axi4_master_tx_compare_obj.arid    &&
  araddr  == axi4_master_tx_compare_obj.araddr  &&
  arlen   == axi4_master_tx_compare_obj.arlen   &&
  arsize  == axi4_master_tx_compare_obj.arsize  &&
  arburst == axi4_master_tx_compare_obj.arburst &&
  arlock  == axi4_master_tx_compare_obj.arlock  &&
  arcache == axi4_master_tx_compare_obj.arcache &&
  arprot  == axi4_master_tx_compare_obj.arprot  &&
  arqos   == axi4_master_tx_compare_obj.arqos   &&
  rdata   == axi4_master_tx_compare_obj.rdata   &&
  rstrb   == axi4_master_tx_compare_obj.rstrb   &&
  rresp   == axi4_master_tx_compare_obj.rresp;

endfunction:do_compare

//--------------------------------------------------------------------------------------------
// Function: do_print method
// Print method can be added to display the data members values
//
// Parameters :
// printer  - uvm_printer
//--------------------------------------------------------------------------------------------
function void axi4_master_tx::do_print(uvm_printer printer);
  super.do_print(printer);
  `uvm_info("------------------------------------------WRITE_ADDRESS_CHANNEL","----------------------------------------",UVM_LOW);
  printer.print_string("awid",awid.name());
  printer.print_field("awaddr",awaddr,$bits(awaddr),UVM_HEX);
  printer.print_string("awlen",awlen.name());
  printer.print_string("awsize",awsize.name());
  printer.print_string("awburst",awburst.name());
  printer.print_string("awlock",awlock.name());
  printer.print_string("awcache",awcache.name());
  printer.print_string("awprot",awprot.name());
  printer.print_field("awqos",awqos,$bits(awqos),UVM_HEX);
  `uvm_info("------------------------------------------WRITE_DATA_CHANNEL","----------------------------------------",UVM_LOW);
  printer.print_field("wdata",wdata,$bits(wdata),UVM_HEX);
  printer.print_field("wstrb",wstrb,$bits(wstrb),UVM_HEX);
  `uvm_info("------------------------------------------WRITE_RESPONSE_CHANNEL","----------------------------------------",UVM_LOW);
  printer.print_string("bid",bid.name());
  printer.print_string("bresp",bresp.name());
  `uvm_info("------------------------------------------READ_ADDRESS_CHANNEL","----------------------------------------",UVM_LOW);
  printer.print_string("arid",arid.name());
  printer.print_field("araddr",araddr,$bits(araddr),UVM_HEX);
  printer.print_string("arlen",arlen.name());
  printer.print_string("arsize",arsize.name());
  printer.print_string("arburst",arburst.name());
  printer.print_string("arlock",arlock.name());
  printer.print_string("arcache",arcache.name());
  printer.print_string("arprot",arprot.name());
  printer.print_field("arqos",arqos,$bits(arqos),UVM_HEX);
  `uvm_info("------------------------------------------READ_DATA_CHANNEL","----------------------------------------",UVM_LOW);
  printer.print_field("rdata",rdata,$bits(rdata),UVM_HEX);
  printer.print_field("rstrb",rstrb,$bits(rstrb),UVM_HEX);
  printer.print_string("rresp",rresp.name());
endfunction : do_print

`endif
