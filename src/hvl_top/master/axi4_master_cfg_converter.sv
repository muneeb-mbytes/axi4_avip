`ifndef AXI4_MASTER_CFG_CONVERTER_INCLUDED_
`define AXI4_MASTER_CFG_CONVERTER_INCLUDED_

//--------------------------------------------------------------------------------------------
// Class: axi4_master_cfg_converter
// Description:
// class for converting the transaction items to struct and vice versa                                                          
//--------------------------------------------------------------------------------------------
class axi4_master_cfg_converter extends uvm_object;
  `uvm_object_utils(axi4_master_cfg_converter)

  //-------------------------------------------------------
  // Externally defined Tasks and Functions
  //-------------------------------------------------------
  extern function new(string name = "axi4_master_cfg_converter");
  extern static function void from_class(input axi4_master_agent_config input_conv,output axi4_transfer_cfg_s output_conv);
  extern function void do_print(uvm_printer printer);

endclass : axi4_master_cfg_converter

//--------------------------------------------------------------------------------------------
// Construct: new
// Parameters:
// name - axi4_master_cfg_converter
//--------------------------------------------------------------------------------------------
function axi4_master_cfg_converter::new(string name = "axi4_master_cfg_converter");
  super.new(name);
endfunction : new

//--------------------------------------------------------------------------------------------
// function: from_write_class
// converting seq_item transactions into struct data items
//--------------------------------------------------------------------------------------------
function void axi4_master_cfg_converter::from_class(input axi4_master_agent_config input_conv, output axi4_transfer_cfg_s output_conv);
  //output_conv.awaddr=input_conv.awaddr;
  // output_conv.araddr=input_conv.araddr;
endfunction: from_class

//--------------------------------------------------------------------------------------------
// Function: do_print method
// Print method can be added to display the data members values
//--------------------------------------------------------------------------------------------
function void axi4_master_cfg_converter:: do_print(uvm_printer printer); 
  axi4_transfer_cfg_s axi4_w_cfg;
  //axi4_r_transfer_cfg_s axi4_r_cfg;
  //printer.print_field("awaddr",axi4_w_cfg.awaddr,$bits(axi4_w_cfg.awaddr),UVM_DEC);
  //printer.print_field("araddr",axi4_r_cfg.araddr,$bits(axi4_r_cfg.araddr),UVM_DEC);
endfunction : do_print

`endif

