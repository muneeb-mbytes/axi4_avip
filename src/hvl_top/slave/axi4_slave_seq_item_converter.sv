`ifndef AXI4_SLAVE_SEQ_ITEM_CONVERTER_INCLUDED_
`define AXI4_SLAVE_SEQ_ITEM_CONVERTER_INCLUDED_

//--------------------------------------------------------------------------------------------
// Class: axi4_slave_seq_item_converter
// Description:
// class for converting the transaction items to struct and vice versa
//--------------------------------------------------------------------------------------------
class axi4_slave_seq_item_converter extends uvm_object;
  `uvm_object_utils(axi4_slave_seq_item_converter)

  //-------------------------------------------------------
  // Externally defined Tasks and Functions
  //-------------------------------------------------------
  extern function new(string name = "axi4_slave_seq_item_converter");
  extern static function void from_write_class(input axi4_slave_tx input_conv, output axi4_write_transfer_char_s output_conv);
  extern static function void from_read_class(input axi4_slave_tx input_conv, output axi4_read_transfer_char_s output_conv);
  extern static function void to_write_class(input axi4_write_transfer_char_s input_conv, output axi4_slave_tx output_conv_h);
  extern static function void to_read_class(input axi4_read_transfer_char_s input_conv, output axi4_slave_tx output_conv_h);
  extern function void do_print(uvm_printer printer);
endclass : axi4_slave_seq_item_converter
//------------------------------------------------------------------------------------------
// Construct: new
//
// Parameters:
// name - axi4_slave_seq_item_converter
//--------------------------------------------------------------------------------------------
function axi4_slave_seq_item_converter::new(string name = "axi4_slave_seq_item_converter");
  super.new(name);
endfunction : new

//--------------------------------------------------------------------------------------------      
// Function: from_write_class                                                                             
// Converting seq_item transactions into struct data items                                          
//                                                                                                  
// Parameters:                                                                                      
// name - axi4_slave_tx, axi4_write_transfer_char_s                                                      
//--------------------------------------------------------------------------------------------      
function void axi4_slave_seq_item_converter::from_write_class(input axi4_slave_tx input_conv,output axi4_write_transfer_char_s output_conv);

  `uvm_info("axi4_slave_seq_item_conv_class",$sformatf("----------------------------------------------------------------------"),UVM_HIGH);
   
  $cast(output_conv.awid,input_conv.awid); 
  `uvm_info("axi4_slave_seq_item_conv_class",$sformatf("After randomize awid =  %b",output_conv.awid),UVM_HIGH);
  
  $cast(output_conv.awlen,input_conv.awlen); 
  `uvm_info("axi4_slave_seq_item_conv_class",$sformatf("After randomize awlen =  %b",output_conv.awlen),UVM_HIGH);
  
  $cast(output_conv.awsize,input_conv.awsize);
  `uvm_info("axi4_slave_seq_item_conv_class",$sformatf("After randomizing awsize =  %b",output_conv.awsize),UVM_HIGH);
  
  $cast(output_conv.awburst,input_conv.awburst);  
  `uvm_info("axi4_slave_seq_item_conv_class",$sformatf("After randomize awburst =  %b",output_conv.awburst),UVM_HIGH);
   
  $cast(output_conv.awlock,input_conv.awlock);
  `uvm_info("axi4_slave_seq_item_conv_class",$sformatf("After randomize awlock =  %b",output_conv.awlock),UVM_HIGH);
 
  $cast(output_conv.awcache,input_conv.awcache);
  `uvm_info("axi4_slave_seq_item_conv_class",$sformatf("After randomizing awcache =  %b",output_conv.awcache),UVM_HIGH);
   
  $cast(output_conv.awprot,input_conv.awprot);
  `uvm_info("axi4_slave_seq_item_conv_class",$sformatf("After randomizing awprot =  %b",output_conv.awprot),UVM_HIGH);
   
  $cast(output_conv.bid,input_conv.bid);   
  `uvm_info("axi4_slave_seq_item_conv_class",$sformatf("After randomize bid =  %b",output_conv.bid),UVM_HIGH);

   output_conv.awqos = input_conv.awqos;   
   `uvm_info("axi4_slave_seq_item_conv_class",$sformatf("after writnig awqos =  %0h",output_conv.awqos),UVM_HIGH);
   
   foreach(input_conv.wdata[i]) begin
     output_conv.wdata[i] = input_conv.wdata[i];
     `uvm_info("axi4_slave_seq_item_conv_class",$sformatf("after writnig wdata = %0h",output_conv.wdata[i]),UVM_HIGH);
   end
   
   foreach(input_conv.wstrb[i]) begin
     output_conv.wstrb[i] = input_conv.wstrb[i];
     `uvm_info("axi4_slave_seq_item_conv_class",$sformatf("after writnig wstrb[%0d] =  %0h",i,output_conv.wstrb[i]),UVM_HIGH);
   end

  $cast(output_conv.bresp,input_conv.bresp);
  `uvm_info("axi4_slave_seq_item_conv_class",$sformatf("After randomize bresp =  %b",output_conv.bresp),UVM_HIGH);                        

  output_conv.awaddr = input_conv.awaddr;
  `uvm_info("axi4_slave_seq_item_conv_class",$sformatf("after writnig awaddr =  %0h",output_conv.awaddr),UVM_HIGH);
  
  output_conv.wait_count_write_address_channel =input_conv.wait_count_write_address_channel ;
  output_conv.wait_count_write_data_channel =input_conv.wait_count_write_data_channel ;
  output_conv.wait_count_write_response_channel =input_conv.wait_count_write_response_channel ;

endfunction : from_write_class
//--------------------------------------------------------------------------------------------      
// Function: from_read_class                                                                             
// Converting seq_item transactions into struct data items                                          
//                                                                                                  
// Parameters:                                                                                      
// name - axi4_slave_tx, axi4_read_transfer_char_s                                                      
//--------------------------------------------------------------------------------------------      

function void axi4_slave_seq_item_converter::from_read_class(input axi4_slave_tx input_conv,output axi4_read_transfer_char_s output_conv);

  $cast(output_conv.arid,input_conv.arid);
  `uvm_info("axi4_slave_seq_item_conv_class",$sformatf("After randomize arid =  %b",output_conv.arid),UVM_HIGH);

  $cast(output_conv.arlen,input_conv.arlen);
  `uvm_info("axi4_slave_seq_item_conv_class",$sformatf("After randomize arlen =  %b",output_conv.arlen),UVM_HIGH);

  $cast(output_conv.arsize,input_conv.arsize);
  `uvm_info("axi4_slave_seq_item_conv_class",$sformatf("After randomize arsize =  %b",output_conv.arsize),UVM_HIGH);

  $cast(output_conv.arburst,input_conv.arburst);
  `uvm_info("axi4_slave_seq_item_conv_class",$sformatf("After randomize arburst =  %b",output_conv.arburst),UVM_HIGH);

  $cast(output_conv.arlock,input_conv.arlock);
  `uvm_info("axi4_slave_seq_item_conv_class",$sformatf("After randomize arlock =  %b",output_conv.arlock),UVM_HIGH);

  $cast(output_conv.arcache,input_conv.arcache);
  `uvm_info("axi4_slave_seq_item_conv_class",$sformatf("After randomize arcache =  %b",output_conv.arcache),UVM_HIGH);

  $cast(output_conv.arprot,input_conv.arprot);
  `uvm_info("axi4_slave_seq_item_conv_class",$sformatf("After randomize arprot =  %b",output_conv.arprot),UVM_HIGH);

  $cast(output_conv.rresp,input_conv.rresp);
  `uvm_info("axi4_slave_seq_item_conv_class",$sformatf("After randomize rresp =  %b",output_conv.rresp),UVM_HIGH);
  
  output_conv.araddr = input_conv.araddr;
  `uvm_info("axi4_slave_seq_item_conv_class",$sformatf("after writnig araddr =  %0h",output_conv.araddr),UVM_HIGH);

  output_conv.arqos = input_conv.arqos;
  `uvm_info("axi4_slave_seq_item_conv_class",$sformatf("after writnig arqos =  %0h",output_conv.arqos),UVM_HIGH);

  foreach(input_conv.rdata[i]) begin
    output_conv.rdata[i] = input_conv.rdata[i];
    `uvm_info("axi4_slave_seq_item_conv_class",$sformatf("after writnig rdata = %0p",output_conv.rdata[i]),UVM_HIGH);
  end

  output_conv.araddr = input_conv.araddr;
  `uvm_info("axi4_slave_seq_item_conv_class",$sformatf("after writnig araddr =  %0h",output_conv.araddr),UVM_HIGH);
  
  output_conv.wait_count_read_address_channel =input_conv.wait_count_read_address_channel ;
  output_conv.wait_count_read_data_channel =input_conv.wait_count_read_data_channel ;

  `uvm_info("axi4_slave_seq_item_conv_class",$sformatf("----------------------------------------------------------------------"),UVM_HIGH);
  
endfunction : from_read_class  

//--------------------------------------------------------------------------------------------      
// Function: to_write_class                                                                               
// Converting struct data items into seq_item transactions                                          
// Parameters:                                                                                      
// name - axi4_slave_tx, axi4_write_transfer_char_s                                                      
//--------------------------------------------------------------------------------------------      


function void axi4_slave_seq_item_converter::to_write_class(input axi4_write_transfer_char_s input_conv, output axi4_slave_tx output_conv_h);

    output_conv_h = new();

  `uvm_info("axi4_slave_seq_item_conv_class",$sformatf("----------------------------------------------------------------------"),UVM_HIGH);
 
  $cast(input_conv.awid,output_conv_h.awid); 
  `uvm_info("axi4_slave_seq_item_conv_class",$sformatf("After randomize awid =  %b",output_conv_h.awid),UVM_HIGH);

  $cast(input_conv.awlen,output_conv_h.awlen);
  `uvm_info("axi4_slave_seq_item_conv_class",$sformatf("After randomize awlen =  %b",output_conv_h.awlen),UVM_HIGH);

  $cast(input_conv.awsize,output_conv_h.awsize);
  `uvm_info("axi4_slave_seq_item_conv_class",$sformatf("After randomizing awsize =  %b",output_conv_h.awsize),UVM_HIGH);

  $cast(input_conv.awburst,output_conv_h.awburst); 
  `uvm_info("axi4_slave_seq_item_conv_class",$sformatf("After randomize awburst =  %b",output_conv_h.awburst),UVM_HIGH);

  $cast(input_conv.awlock,output_conv_h.awlock);
  `uvm_info("axi4_slave_seq_item_conv_class",$sformatf("After randomize awlock =  %b",output_conv_h.awlock),UVM_HIGH);

  $cast(input_conv.awcache,output_conv_h.awcache);
  `uvm_info("axi4_slave_seq_item_conv_class",$sformatf("After randomizing awcache =  %b",output_conv_h.awcache),UVM_HIGH);

  $cast(input_conv.awprot,output_conv_h.awprot);
  `uvm_info("axi4_slave_seq_item_conv_class",$sformatf("After randomizing awprot =  %b",output_conv_h.awprot),UVM_HIGH);

  $cast(input_conv.bid,output_conv_h.bid);
  `uvm_info("axi4_slave_seq_item_conv_class",$sformatf("After randomize bid =  %b",output_conv_h.bid),UVM_HIGH);

  $cast(input_conv.bresp,output_conv_h.bresp);
  `uvm_info("axi4_slave_seq_item_conv_class",$sformatf("After randomize bresp =  %b",output_conv_h.bresp),UVM_HIGH);

  input_conv.awaddr = output_conv_h.awaddr;
  `uvm_info("axi4_slave_seq_item_conv_class",$sformatf("after writnig awaddr =  %0h",output_conv_h.awaddr),UVM_HIGH);

  input_conv.awqos = output_conv_h.awqos;
  `uvm_info("axi4_slave_seq_item_conv_class",$sformatf("after writnig awqos =  %0h",output_conv_h.awqos),UVM_HIGH);

  //input_conv.wdata = output_conv_h.wdata;
  //`uvm_info("axi4_slave_seq_item_conv_class",$sformatf("after writnig wdata =  %0h",output_conv_h.wdata),UVM_HIGH);

  //input_conv.wstrb = output_conv_h.wstrb;
  //`uvm_info("axi4_slave_seq_item_conv_class",$sformatf("after writnig wstrb =  %0h",output_conv_h.wstrb),UVM_HIGH);

  foreach(output_conv_h.wdata[i]) begin
    input_conv.wdata[i] = output_conv_h.wdata[i];
    `uvm_info("axi4_master_seq_item_conv_class",$sformatf("after writnig wdata =  %0p",output_conv_h.wdata),UVM_HIGH);
  end

  foreach(output_conv_h.wstrb[i]) begin
    input_conv.wstrb[i] = output_conv_h.wstrb[i];
    `uvm_info("axi4_master_seq_item_conv_class",$sformatf("after writnig wstrb = %0p",output_conv_h.wstrb[i]),UVM_HIGH);
  end
endfunction : to_write_class


//--------------------------------------------------------------------------------------------      
// Function: to_read_class                                                                               
// Converting struct data items into seq_item transactions                                          
// Parameters:                                                                                      
// name - axi4_slave_tx, axi4_read_transfer_char_s                                                      
//--------------------------------------------------------------------------------------------      
function void axi4_slave_seq_item_converter::to_read_class( input axi4_read_transfer_char_s input_conv, output axi4_slave_tx output_conv_h);

  output_conv_h = new();

  $cast(input_conv.arid,output_conv_h.arid);
  `uvm_info("axi4_slave_seq_item_conv_class",$sformatf("After randomize arid =  %b",output_conv_h.arid),UVM_HIGH);

  $cast(input_conv.arlen,output_conv_h.arlen);
  `uvm_info("axi4_slave_seq_item_conv_class",$sformatf("After randomize arlen =  %b",output_conv_h.arlen),UVM_HIGH);

  $cast(input_conv.arsize,output_conv_h.arsize);
  `uvm_info("axi4_slave_seq_item_conv_class",$sformatf("After randomize arsize =  %b",output_conv_h.arsize),UVM_HIGH);

  $cast(input_conv.arburst,output_conv_h.arburst);
  `uvm_info("axi4_slave_seq_item_conv_class",$sformatf("After randomize arburst =  %b",output_conv_h.arburst),UVM_HIGH);

  $cast(input_conv.arlock,output_conv_h.arlock);
  `uvm_info("axi4_slave_seq_item_conv_class",$sformatf("After randomize arlock =  %b",output_conv_h.arlock),UVM_HIGH);

  $cast(input_conv.arcache,output_conv_h.arcache);
  `uvm_info("axi4_slave_seq_item_conv_class",$sformatf("After randomize arcache =  %b",output_conv_h.arcache),UVM_HIGH);

  $cast(input_conv.arprot,output_conv_h.arprot);
  `uvm_info("axi4_slave_seq_item_conv_class",$sformatf("After randomize arprot =  %b",output_conv_h.arprot),UVM_HIGH);

  $cast(input_conv.rresp,output_conv_h.rresp);
  `uvm_info("axi4_slave_seq_item_conv_class",$sformatf("After randomize rresp =  %b",output_conv_h.rresp),UVM_HIGH);
  
  input_conv.araddr = output_conv_h.araddr;
  `uvm_info("axi4_slave_seq_item_conv_class",$sformatf("after writnig araddr =  %0h",output_conv_h.araddr),UVM_HIGH);

  input_conv.arqos = output_conv_h.arqos;
  `uvm_info("axi4_slave_seq_item_conv_class",$sformatf("after writnig arqos =  %0h",output_conv_h.arqos),UVM_HIGH);

  foreach(output_conv_h.rdata[i]) begin
    input_conv.rdata[i] = output_conv_h.rdata[i];
    `uvm_info("axi4_slave_seq_item_conv_class",$sformatf("after writnig rdata =  %0p",output_conv_h.rdata),UVM_HIGH);
  end

  input_conv.araddr = output_conv_h.araddr;
  `uvm_info("axi4_slave_seq_item_conv_class",$sformatf("after writnig araddr =  %0h",output_conv_h.araddr),UVM_HIGH);

  `uvm_info("axi4_slave_seq_item_conv_class",$sformatf("----------------------------------------------------------------------"),UVM_HIGH);
endfunction : to_read_class

//--------------------------------------------------------------------------------------------
// Function: do_print method
// Print method can be added to display the data members values
//--------------------------------------------------------------------------------------------
function void axi4_slave_seq_item_converter::do_print(uvm_printer printer);


  axi4_write_transfer_char_s axi4_w_st;
  axi4_read_transfer_char_s axi4_r_st;
  super.do_print(printer);

  printer.print_field("awid",axi4_w_st.awid,$bits(axi4_w_st.awid),UVM_HEX);
  printer.print_field("awlen",axi4_w_st.awlen,$bits(axi4_w_st.awlen),UVM_HEX);
  printer.print_field("awsize",axi4_w_st.awsize,$bits(axi4_w_st.awsize),UVM_DEC);
  printer.print_field("awburst",axi4_w_st.awburst,$bits(axi4_w_st.awburst),UVM_DEC);
  printer.print_field("awlock",axi4_w_st.awlock,$bits(axi4_w_st.awlock),UVM_DEC);
  printer.print_field("awcache",axi4_w_st.awcache,$bits(axi4_w_st.awcache),UVM_DEC);
  printer.print_field("awprot",axi4_w_st.awprot,$bits(axi4_w_st.awprot),UVM_HEX);
  printer.print_field("bid",axi4_w_st.bid,$bits(axi4_w_st.bid),UVM_HEX);
  //printer.print_field("awaddr",axi4_w_st.awaddr,$bits(axi4_w_st.awaddr),UVM_HEX);
  //printer.print_field("awqos",axi4_w_st.awqos,$bits(axi4_w_st.awqos),UVM_HEX);
  //printer.print_field("wdata",axi4_w_st.wdata,$bits(axi4_w_st.wdata),UVM_HEX);
  //printer.print_field("wstrb",axi4_w_st.wstrb,$bits(axi4_w_st.wstrb),UVM_HEX);
 
  printer.print_field("arid",axi4_r_st.arid,$bits(axi4_r_st.arid),UVM_HEX);
  printer.print_field("arlen",axi4_r_st.arlen,$bits(axi4_r_st.arlen),UVM_HEX);
  printer.print_field("arsize",axi4_r_st.arsize,$bits(axi4_r_st.arsize),UVM_DEC);
  printer.print_field("arburst",axi4_r_st.arburst,$bits(axi4_r_st.arburst),UVM_DEC);
  printer.print_field("arlock",axi4_r_st.arlock,$bits(axi4_r_st.arlock),UVM_DEC);
  printer.print_field("arcache",axi4_r_st.arcache,$bits(axi4_r_st.arcache),UVM_DEC);
  printer.print_field("arprot",axi4_r_st.arprot,$bits(axi4_r_st.arprot),UVM_HEX);
  printer.print_field("rresp",axi4_r_st.rresp,$bits(axi4_r_st.rresp),UVM_HEX);
  //printer.print_field("araddr",axi4_r_st.araddr,$bits(axi4_r_st.araddr),UVM_HEX);
  //printer.print_field("arqos",axi4_r_st.arqos,$bits(axi4_r_st.arqos),UVM_HEX);
  //printer.print_field("rdata",axi4_r_st.rdata,$bits(axi4_r_st.rdata),UVM_HEX);
 
  foreach(axi4_r_st.rdata[i]) begin
    printer.print_field($sformatf("rdata[%0d]",i),axi4_r_st.rdata[i],$bits(axi4_r_st.rdata[i]),UVM_HEX);
  end

endfunction : do_print


`endif
