`ifndef AXI4_SLAVE_TX_INCLUDED_
`define AXI4_SLAVE_TX_INCLUDED_

//--------------------------------------------------------------------------------------------
// Class: axi4_slave_tx
//  This class holds the data items required to drive stimulus to dut
//  and also holds methods that manipulate those data items
//--------------------------------------------------------------------------------------------
class axi4_slave_tx extends uvm_sequence_item;
  
  `uvm_object_utils(axi4_slave_tx)
  
  //-------------------------------------------------------
  // WRITE ADDRESS CHANNEL SIGNALS
  //-------------------------------------------------------
  //Variable : awaddr
  //Address selected in axi_slave
  bit [ADDRESS_WIDTH-1:0] awaddr;

  //Variable : awid
  //Used to identify the write transaction for the adress
  awid_e awid;

  //Variable : alen
  //Used to represent the no.of beats in a transaction
  bit [LENGTH-1:0]awlen;

  //Variable : awsize
  //Used to send the write address size
  awsize_e awsize;

  //Variable : awburst
  //Used to send the address burst type
  awburst_e awburst;

  //Variable : awready
  //Used to accept the valid address
  //bit awready;
  
  //Variable : awvalid
  //Used to accept the valid address
  //bit awvalid;

  //Variable : awlock
  //Used to send the  write address lock
  awlock_e awlock;

  //Variable : awcache
  //Used to send the write address cache
  awcache_e awcache;

  //Variable : awqos
  //Used to send the write address quality os service
  bit awqos;

  //Variable : addr_write_prot
  //used for different access
  awprot_e awprot;

  //Variable : endian
  //Used to store data in adress location
  endian_e endian;
  
 int wait_count_write_address_channel;
 int wait_count_write_data_channel;
 int wait_count_write_response_channel;
 int wait_count_read_address_channel;
 int wait_count_read_data_channel;
 
 int outstanding_write_tx;
 int outstanding_read_tx;
 int no_of_wait_states;

  //-------------------------------------------------------
  // WRITE DATA CHANNEL SIGNALS
  //-------------------------------------------------------
  //Variable : wdata
  //Used to send the write data 
  bit [DATA_WIDTH-1:0] wdata;

  //Variable : wstrb
  //Used to hold the valid data byte lanes
  bit [(DATA_WIDTH/8)-1:0] wstrb;

  //Variable : wlast
  //Used to represent the last byte of the transaction
  //bit wlast;

  //Variable : wready
  //Used to accept the valid data
  //bit wready;

  //Variable : wvalid
  //Used to accept the valid address
  //bit wvalid;

  //-------------------------------------------------------
  // WRITE RESPONSE CHANNEL SIGNALS
  //-------------------------------------------------------
  //Variable : bid
  //Used to send the response to particular id
  rand bid_e bid;

  //Variable : bresp
  //Used to send the write response for the transaction
  rand bresp_e bresp;

  //Variable : bready
  //Used to accept write response are  valid data
  //bit bready;

  //Variable : bvalid
  //Used to accept the write transaction has valid data
  //bit bvalid;

  //-------------------------------------------------------
  // READ ADDRESS CHANNEL SIGNALS
  //-------------------------------------------------------
  //Variable : arid
  //Used to identify the read transaction for the adress
  rand arid_e arid;
  
  //Variable : araddr
  //Address selected in axi_slave
  rand bit [ADDRESS_WIDTH-1:0] araddr;

  //Variable : arlen
  //Used to represent the no.of beats in a transaction
  rand bit [LENGTH-1:0]arlen;

  //Variable : arsize
  //Used to send the write address size
  rand arsize_e arsize;

  //Variable : arburst
  //Used to send the address burst type
  rand arburst_e arburst;
 
  //Variable : awlock
  //Used to send the  write address lock
  rand arlock_e arlock;

  //Variable : awcache
  //Used to send the write address cache
  rand arcache_e arcache;

  //Variable : arprot
  //used for different access
  rand arprot_e arprot;

  //Variable : arready
  //Used to accept the valid address
  //bit arready;
  
  //Variable : arvalid
  //Used to accept the valid address
  //bit arvalid;

  //Variable : arqos
  //Used to send the read address quality of service
  rand bit arqos;

  //-------------------------------------------------------
  // READ DATA CHANNEL SIGNALS
  //-------------------------------------------------------
  //Variable : rid
  //Used to identify the read data and response
  rand rid_e rid;

  //Variable : rdata
  //Used to send the read data 
  rand bit [DATA_WIDTH-1:0] rdata [$:DATA_WIDTH];

  //Variable : rlast
  //Used to represent the last byte of the transaction
  //rand bit rlast;

  //Variable : rready
  //Used to accept the valid data
  //bit rready;

  //Variable : rvalid
  //Used to accept the valid address
  //bit rvalid;

  //Variable : rresp
  //Used to store the read response
  rand rresp_e rresp ;

  //Variable : no_of_wait_states
  //Used to decide the number of wait states
  //rand bit [2:0]no_of_wait_states;

  //-------------------------------------------------------
  // Constraints
  //-------------------------------------------------------
  //Constraint : rdata_c1
  //Adding constraint to restrict the read data based on awlength
  constraint rdata_c1 { rdata.size() == arlen+1; 
                      }
  

  //Constraint : bresp
  //Adding constraint to select the type of write response
  constraint bresp_c1 {soft bresp == WRITE_OKAY;
                      }

  //Constraint : rresp
  //Adding constraint to select the type of read response
  constraint rresp_c1 {soft rresp == READ_OKAY;
                      }
  //To randomise the wait states in range of 0 to 3
  constraint wait_states_c1 {soft no_of_wait_states inside {[0:3]};}
                    
  //-------------------------------------------------------
  // Externally defined Tasks and Functions
  //-------------------------------------------------------
  extern function new(string name = "axi4_slave_tx");
  extern function void do_copy(uvm_object rhs);
  extern function bit do_compare (uvm_object rhs, uvm_comparer comparer);
  extern function void do_print(uvm_printer printer);
endclass : axi4_slave_tx

//--------------------------------------------------------------------------------------------
// Construct: new
// initializes the class object
//
// Parameters:
// name - axi4_slave_tx
//--------------------------------------------------------------------------------------------
function axi4_slave_tx::new(string name = "axi4_slave_tx");
  super.new(name);
endfunction : new

//--------------------------------------------------------------------------------------------
// Function: do_copy
// Compare method is implemented using handle rhs
//
// Parameters:
// rhs - handle
//--------------------------------------------------------------------------------------------
function void axi4_slave_tx::do_copy (uvm_object rhs);
  axi4_slave_tx axi_slave_tx_copy_obj;

  if($cast(axi_slave_tx_copy_obj,rhs )) begin
    `uvm_fatal("do_copy","cast of the rhs object failed")
  end

  super.do_copy(rhs);
  //WRITE ADDRESS CHANNEL
  awaddr  = axi_slave_tx_copy_obj.awaddr;
  awid    = axi_slave_tx_copy_obj.awid;
  awlen   = axi_slave_tx_copy_obj.awlen;
  awsize  = axi_slave_tx_copy_obj.awsize;
  awburst = axi_slave_tx_copy_obj.awburst;
  //awready = axi_slave_tx_copy_obj.awready;
  //awvalid = axi_slave_tx_copy_obj.awvalid;
  awlock  = axi_slave_tx_copy_obj.awlock;
  awcache = axi_slave_tx_copy_obj.awcache;
  awqos   = axi_slave_tx_copy_obj.awqos;
  awprot  = axi_slave_tx_copy_obj.awprot;

  //WRITE DATA CHANNEL
  wdata   = axi_slave_tx_copy_obj.wdata;
  wstrb   = axi_slave_tx_copy_obj.wstrb;
  //wready  = axi_slave_tx_copy.obj.wready;
  //wvalid  = axi_slave_tx_copy.obj.wvalid;
  
  //WRITE RESPONSE CHANNEL
  bid     = axi_slave_tx_copy_obj.bid;
  bresp   = axi_slave_tx_copy_obj.bresp;
  //bvalid  = axi_slave_tx_copy_obj.bvalid;
  //bready  = axi_slave_tx_copy_obj.bready;
  
  //READ ADDRESS CHANNEL
  araddr  = axi_slave_tx_copy_obj.araddr;
  arid    = axi_slave_tx_copy_obj.arid;
  arlen   = axi_slave_tx_copy_obj.arlen;
  arsize  = axi_slave_tx_copy_obj.arsize;
  arburst = axi_slave_tx_copy_obj.arburst;
  //arready = axi_slave_tx_copy_obj.arready;
  //arvalid = axi_slave_tx_copy_obj.arvalid;
  arlock  = axi_slave_tx_copy_obj.arlock;
  arcache = axi_slave_tx_copy_obj.arcache;
  arqos   = axi_slave_tx_copy_obj.arqos;
  arprot  = axi_slave_tx_copy_obj.arprot;

  //READ DATA CHANNEL
  rid   = axi_slave_tx_copy_obj.rid;
  rdata = axi_slave_tx_copy_obj.rdata;
  rresp = axi_slave_tx_copy_obj.rresp;
  //rready  = axi_slave_tx_copy.obj.rready;
  //rvalid  = axi_slave_tx_copy.obj.rvalid;
endfunction : do_copy

//--------------------------------------------------------------------------------------------
//  Function: do_compare
//  Compare method is implemented using handle rhs
//
//  Parameters:
//  comparer - handle
//--------------------------------------------------------------------------------------------
function bit axi4_slave_tx::do_compare (uvm_object rhs, uvm_comparer comparer);
  axi4_slave_tx axi_slave_tx_compare_obj;

  if(!$cast(axi_slave_tx_compare_obj,rhs)) begin
    `uvm_fatal("FATAL_axi_SLAVE_TX_DO_COMPARE_FAILED","cast of the rhs object failed")
  return 0;
  end

  return super.do_compare(axi_slave_tx_compare_obj, comparer) &&
  //WRITE ADDRESS CHANNEL
  awaddr  == axi_slave_tx_compare_obj.awaddr &&   
  awid    == axi_slave_tx_compare_obj.awid   &&
  awlen   == axi_slave_tx_compare_obj.awlen  &&
  awsize  == axi_slave_tx_compare_obj.awsize &&
  awburst == axi_slave_tx_compare_obj.awburst &&
  //awready == axi_slave_tx_compare_obj.awready &&
  //awvalid == axi_slave_tx_compare_obj.awvalid &&
  awlock  == axi_slave_tx_compare_obj.awlock &&
  awcache == axi_slave_tx_compare_obj.awcache &&
  awqos   == axi_slave_tx_compare_obj.awqos  &&
  awprot  == axi_slave_tx_compare_obj.awprot &&

  //WRITE DATA CHANNEL
  wdata == axi_slave_tx_compare_obj.wdata  &&
  wstrb == axi_slave_tx_compare_obj.wstrb  &&
  //wready  == axi_slave_tx_compare.obj.wready &&
  //wvalid  == axi_slave_tx_compare.obj.wvalid &&
  
  //WRITE RESPONSE CHANNEL
  bid   == axi_slave_tx_compare_obj.bid    &&
  bresp == axi_slave_tx_compare_obj.bresp  &&
  //bvalid  == axi_slave_tx_compare_obj.bvalid &&
  //bready  == axi_slave_tx_compare_obj.bready &&

  //READ ADDRESS CHANNEL
  araddr  == axi_slave_tx_compare_obj.araddr &&
  arid    == axi_slave_tx_compare_obj.arid   &&
  arlen   == axi_slave_tx_compare_obj.arlen  &&
  arsize  == axi_slave_tx_compare_obj.arsize &&
  arburst == axi_slave_tx_compare_obj.arburst &&
  //arready == axi_slave_tx_compare_obj.arready &&
  //arvalid == axi_slave_tx_compare_obj.arvalid &&
  arlock  == axi_slave_tx_compare_obj.arlock &&
  arcache == axi_slave_tx_compare_obj.arcache &&
  arqos   == axi_slave_tx_compare_obj.arqos  &&
  arprot  == axi_slave_tx_compare_obj.arprot &&

  //READ DATA CHANNEL
  rid   == axi_slave_tx_compare_obj.rid  &&  
  rdata == axi_slave_tx_compare_obj.rdata && 
  rresp == axi_slave_tx_compare_obj.rresp;
  //rready == axi_slave_tx_compare.obj.rready &&
  //rvalid == axi_slave_tx_compare.obj.rvalid ;
endfunction : do_compare

//--------------------------------------------------------------------------------------------
// Function: do_print method
// Print method can be added to display the data members values
//--------------------------------------------------------------------------------------------
function void axi4_slave_tx::do_print(uvm_printer printer);
  super.do_print(printer);

  `uvm_info("------------------------------------------WRITE_ADDRESS_CHANNEL","-------------------------------------",UVM_LOW);
  printer.print_string("awid",awid.name());
  printer.print_field("awaddr",awaddr,$bits(awaddr),UVM_HEX);
  printer.print_field("awlen",awlen,$bits(awlen),UVM_HEX);
  printer.print_string("awsize",awsize.name());
  printer.print_string("awburst",awburst.name());
  printer.print_string("awlock",awlock.name());
  printer.print_string("awcache",awcache.name());
  printer.print_string("awprot",awprot.name());
  printer.print_field("awqos",awqos,$bits(awqos),UVM_HEX);
  `uvm_info("------------------------------------------WRITE_DATA_CHANNEL","----------------------------------------",UVM_LOW);
  printer.print_field("wdata",wdata,$bits(wdata),UVM_HEX);
  printer.print_field("wstrb",wstrb,$bits(wstrb),UVM_HEX);
  `uvm_info("------------------------------------------WRITE_RESPONSE_CHANNEL","------------------------------------",UVM_LOW);
  printer.print_string("bid",bid.name());
  printer.print_string("bresp",bresp.name());
  `uvm_info("------------------------------------------READ_ADDRESS_CHANNEL","--------------------------------------",UVM_LOW);
  printer.print_string("arid",arid.name());
  printer.print_field("araddr",araddr,$bits(araddr),UVM_HEX);
  printer.print_field("arlen",arlen,$bits(arlen),UVM_HEX);
  printer.print_string("arsize",arsize.name());
  printer.print_string("arburst",arburst.name());
  printer.print_string("arlock",arlock.name());
  printer.print_string("arcache",arcache.name());
  printer.print_string("arprot",arprot.name());
  printer.print_field("arqos",arqos,$bits(arqos),UVM_HEX);
  `uvm_info("------------------------------------------READ_DATA_CHANNEL","---------------------------------------",UVM_LOW);
  printer.print_field("rdata",rdata.size(),UVM_HEX);
  printer.print_string("rresp",rresp.name());

  printer.print_field("no_of_wait_states",no_of_wait_states,$bits(no_of_wait_states),UVM_HEX);
endfunction : do_print

`endif

