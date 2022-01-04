`ifndef AXI4_GLOBALS_PKG_INCLUDED_
`define AXI4_GLOBALS_PKG_INCLUDED_

//--------------------------------------------------------------------------------------------
// Package: axi4_globals_pkg
// Used for storing enums, parameters and defines
//--------------------------------------------------------------------------------------------
package axi4_globals_pkg;

  //Parameter : MASTER_AGENT_ACTIVE
  //Used to set the master agent either active or passive
  parameter bit MASTER_AGENT_ACTIVE = 1;

  //Parameter : SLAVE_AGENT_ACTIVE
  //Used to set the slave agent either active or passive
  parameter bit SLAVE_AGENT_ACTIVE = 1;

  parameter int NO_OF_MASTERS = 1;

  //Parameter : NO_OF_SLAVES
  //Used to set number of slaves required
  parameter int NO_OF_SLAVES = 1;

  //Parameter : ADDRESS_WIDTH
  //Used to set the address width to the address bus
  //Maximum Value is 32
  parameter int ADDRESS_WIDTH = 32;

  //Parameter : DATA_WIDTH
  //Used to set the data width 
  //Maximum Value is 8
  parameter int DATA_WIDTH = 32;

  //Parameter : SLAVE_MEMORY_SIZE
  //Sets the memory size of the slave in KB
  parameter int SLAVE_MEMORY_SIZE = 12;

  //Parameter : SLAVE_MEMORY_GAP
  //Sets the memory gap size of the slave
  parameter int SLAVE_MEMORY_GAP = 2;

  //Parameter : MEMORY_WIDTH
  //Sets the width it can store in each location
  parameter int MEMORY_WIDTH = 8;


  typedef enum bit [7:0]{
    WRITE_LEN_FIXED,
    WRITE_LEN_WRAP,
    WRITE_LEN_INCR
  } awlen_e;

  
  typedef enum bit [7:0]{
    READ_LEN_FIXED,
    READ_LEN_WRAP,
    READ_LEN_INCR
  } arlen_e;


  typedef enum bit [1:0] {
    WRITE_FIXED     = 2'b00,
    WRITE_INCR      = 2'b01,
    WRITE_WRAP      = 2'b10,
    WRITE_RESERVED  = 2'b11
  } awburst_e;

  
  typedef enum bit [1:0] {
    READ_FIXED     = 2'b00,
    READ_INCR      = 2'b01,
    READ_WRAP      = 2'b10,
    READ_RESERVED  = 2'b11
  } arburst_e;


  //-------------------------------------------------------
  // Enum : transfer_size_e
  //  Used to declare enum type for all transfer sizes
  //-------------------------------------------------------
  typedef enum bit[2:0]{
    WRITE_BYTE_1   = 3'b000,
    WRITE_BYTE_2   = 3'b001,
    WRITE_BYTE_4   = 3'b010,
    WRITE_BYTE_8   = 3'b011,
    WRITE_BYTE_16  = 3'b100,
    WRITE_BYTE_32  = 3'b101,
    WRITE_BYTE_64  = 3'b110,
    WRITE_BYTE_128 = 3'b111
  } awsize_e;

 //-------------------------------------------------------
  // Enum : transfer_size_e
  //  Used to declare enum type for all transfer sizes
  //-------------------------------------------------------
  typedef enum bit[2:0]{
    READ_BYTE_1   = 3'b000,
    READ_BYTE_2   = 3'b001,
    READ_BYTE_4   = 3'b010,
    READ_BYTE_8   = 3'b011,
    READ_BYTE_16  = 3'b100,
    READ_BYTE_32  = 3'b101,
    READ_BYTE_64  = 3'b110,
    READ_BYTE_128 = 3'b111
  } arsize_e;

  typedef enum bit {
    WRITE_NORMAL_ACCESS     = 1'b0,
    WRITE_EXCLUSIVE_ACCESS  = 1'b1
  } awlock_e;

  typedef enum bit {
    READ_NORMAL_ACCESS     = 1'b0,
    READ_EXCLUSIVE_ACCESS  = 1'b1
  } arlock_e;

  typedef enum bit [3:0] {
    WRITE_BUFFERABLE,
    WRITE_MODIFIABLE,
    WRITE_OTHER_ALLOCATE,
    WRITE_ALLOCATE
  } awcache_e;


  typedef enum bit [3:0] {
    READ_BUFFERABLE,
    READ_MODIFIABLE,
    READ_OTHER_ALLOCATE,
    READ_ALLOCATE
  } arcache_e;



  //-------------------------------------------------------
  // Enum : endian_e
  //  Used to declare enum type for the endians
  //-------------------------------------------------------
  typedef enum bit{
    LITTLE_ENDIAN    = 1'b0,
    BIG_ENDIAN      = 1'b1
  } endian_e;

    
  //-------------------------------------------------------
  // Enum : protection_type_e 
  //  Used to declare the type ofprotection of the 
  //  transaction
  //-------------------------------------------------------
  typedef enum bit[2:0]{
    WRITE_NORMAL_SECURE_DATA              = 3'b000,
    WRITE_NORMAL_SECURE_INSTRUCTION       = 3'b001,
    WRITE_NORMAL_NONSECURE_DATA           = 3'b010,
    WRITE_NORMAL_NONSECURE_INSTRUCTION    = 3'b011,
    WRITE_PRIVILEGED_SECURE_DATA          = 3'b100,
    WRITE_PRIVILEGED_SECURE_INSTRUCTION   = 3'b101,
    WRITE_PRIVILEGED_NONSECURE_DATA       = 3'b110,
    WRITE_PRIVILEGED_NONSECURE_INSTUCTION = 3'b111
  } awprot_e;

  //-------------------------------------------------------
  // Enum : protection_type_e 
  //  Used to declare the type of protection of the 
  //  transaction
  //-------------------------------------------------------
  typedef enum bit[2:0]{
    READ_NORMAL_SECURE_DATA              = 3'b000,
    READ_NORMAL_SECURE_INSTRUCTION       = 3'b001,
    READ_NORMAL_NONSECURE_DATA           = 3'b010,
    READ_NORMAL_NONSECURE_INSTRUCTION    = 3'b011,
    READ_PRIVILEGED_SECURE_DATA          = 3'b100,
    READ_PRIVILEGED_SECURE_INSTRUCTION   = 3'b101,
    READ_PRIVILEGED_NONSECURE_DATA       = 3'b110,
    READ_PRIVILEGED_NONSECURE_INSTUCTION = 3'b111
  } arprot_e;


  //-------------------------------------------------------
  // Enum : slave_no_e
  //  Used to declare the slave number by assigning the value for encoding
  //-------------------------------------------------------
  typedef enum bit [15:0] {
    AWID_0  = 16'b0000_0000_0000_0001,
    AWID_1  = 16'b0000_0000_0000_0010,
    AWID_2  = 16'b0000_0000_0000_0100,
    AWID_3  = 16'b0000_0000_0000_1000,
    AWID_4  = 16'b0000_0000_0001_0000,
    AWID_5  = 16'b0000_0000_0010_0000,
    AWID_6  = 16'b0000_0000_0100_0000,
    AWID_7  = 16'b0000_0000_1000_0000,
    AWID_8  = 16'b0000_0001_0000_0000,
    AWID_9  = 16'b0000_0010_0000_0000,
    AWID_10 = 16'b0000_0100_0000_0000,
    AWID_11 = 16'b0000_1000_0000_0000,
    AWID_12 = 16'b0001_0000_0000_0000,
    AWID_13 = 16'b0010_0000_0000_0000,
    AWID_14 = 16'b0100_0000_0000_0000,
    AWID_15 = 16'b1000_0000_0000_0000
  } awid_e;

  typedef enum bit [15:0] {
    BID_0  = 16'b0000_0000_0000_0001,
    BID_1  = 16'b0000_0000_0000_0010,
    BID_2  = 16'b0000_0000_0000_0100,
    BID_3  = 16'b0000_0000_0000_1000,
    BID_4  = 16'b0000_0000_0001_0000,
    BID_5  = 16'b0000_0000_0010_0000,
    BID_6  = 16'b0000_0000_0100_0000,
    BID_7  = 16'b0000_0000_1000_0000,
    BID_8  = 16'b0000_0001_0000_0000,
    BID_9  = 16'b0000_0010_0000_0000,
    BID_10 = 16'b0000_0100_0000_0000,
    BID_11 = 16'b0000_1000_0000_0000,
    BID_12 = 16'b0001_0000_0000_0000,
    BID_13 = 16'b0010_0000_0000_0000,
    BID_14 = 16'b0100_0000_0000_0000,
    BID_15 = 16'b1000_0000_0000_0000
  } bid_e;

  
  //-------------------------------------------------------
  // Enum : slave_no_e
  //  Used to declare the slave number by assigning the value for encoding
  //-------------------------------------------------------
  typedef enum bit [15:0] {
    ARID_0  = 16'b0000_0000_0000_0001,
    ARID_1  = 16'b0000_0000_0000_0010,
    ARID_2  = 16'b0000_0000_0000_0100,
    ARID_3  = 16'b0000_0000_0000_1000,
    ARID_4  = 16'b0000_0000_0001_0000,
    ARID_5  = 16'b0000_0000_0010_0000,
    ARID_6  = 16'b0000_0000_0100_0000,
    ARID_7  = 16'b0000_0000_1000_0000,
    ARID_8  = 16'b0000_0001_0000_0000,
    ARID_9  = 16'b0000_0010_0000_0000,
    ARID_10 = 16'b0000_0100_0000_0000,
    ARID_11 = 16'b0000_1000_0000_0000,
    ARID_12 = 16'b0001_0000_0000_0000,
    ARID_13 = 16'b0010_0000_0000_0000,
    ARID_14 = 16'b0100_0000_0000_0000,
    ARID_15 = 16'b1000_0000_0000_0000
  } arid_e;


  typedef enum bit [15:0] {
    RID_0  = 16'b0000_0000_0000_0001,
    RID_1  = 16'b0000_0000_0000_0010,
    RID_2  = 16'b0000_0000_0000_0100,
    RID_3  = 16'b0000_0000_0000_1000,
    RID_4  = 16'b0000_0000_0001_0000,
    RID_5  = 16'b0000_0000_0010_0000,
    RID_6  = 16'b0000_0000_0100_0000,
    RID_7  = 16'b0000_0000_1000_0000,
    RID_8  = 16'b0000_0001_0000_0000,
    RID_9  = 16'b0000_0010_0000_0000,
    RID_10 = 16'b0000_0100_0000_0000,
    RID_11 = 16'b0000_1000_0000_0000,
    RID_12 = 16'b0001_0000_0000_0000,
    RID_13 = 16'b0010_0000_0000_0000,
    RID_14 = 16'b0100_0000_0000_0000,
    RID_15 = 16'b1000_0000_0000_0000
  } rid_e;

  typedef enum bit [1:0] {
    WRITE_OKAY   = 2'b00,
    WRITE_EXOKAY = 2'b01,
    WRITE_SLVERR = 2'b10,
    WRITE_DECERR = 2'b11
  } bresp_e;

  
  typedef enum bit [1:0] {
    READ_OKAY   = 2'b00,
    READ_EXOKAY = 2'b01,
    READ_SLVERR = 2'b10,
    READ_DECERR = 2'b11
  } rresp_e;



  //-------------------------------------------------------
  // Struct : apb_transfer_char_s
  //  This struct datatype consists of all signals which 
  //  are used for seq item conversion
  //-------------------------------------------------------
  typedef struct {
  
    //Write_address_channel
    bit [15:0]              awid;
    bit [7:0]               awlen;
    bit [2:0]               awsize;
    bit [1:0]               awburst;
    bit                     awlock;
    bit [3:0]               awcache;
    bit [2:0]               awprot;
    bit                     awvalid;
    bit	                    awready;

    //Write_data_channel
    bit [DATA_WIDTH-1:0]     wdata;
    bit [(DATA_WIDTH/8)-1:0] wstrb;
    //bit                      wlast;
    
    //Write Response Channel
    bit [15:0] bid;
    bit [1:0] bresp;
  
  }axi4_w_transfer_char_s; 
  
  typedef struct {

  //Read Address Channel
    bit [15:0]              arid      ;
    bit [7:0]               arlen     ;
    bit [2:0]               arsize    ;
    bit [1:0]               arburst   ;
    bit                     arlock    ;
    bit [3:0] arcache   ;
    bit [2:0] arprot    ;
    bit [3:0] arqos     ;
    
    //Read Data Channel
    bit     [15:0] rid       ;
    bit     [DATA_WIDTH-1: 0] rdata     ;
    bit     [(DATA_WIDTH/8)-1: 0] rstrb     ;
    bit          [1:0] rresp; 
  } axi4_r_transfer_char_s;

  //-------------------------------------------------------
  // Struct : apb_cfg_char_s
  //  This struct datatype consists of all configurations
  //  which are used for seq item conversion
  //-------------------------------------------------------
  typedef struct{
    bit [ADDRESS_WIDTH-1:0] min_address;
    bit [ADDRESS_WIDTH-1:0] max_address;
    bit [ADDRESS_WIDTH-1:0] awaddr;
    bit [ADDRESS_WIDTH-1:0] araddr;
  } axi4_transfer_cfg_s;


  //Variable: AW
  //Indicates AXI Address width 
  //parameter int ADDRESS_WIDTH = 32;

  //Variable: IW
  //Indicates AXI ID width 
  //parameter int ID_WIDTH = 4;

  //Variable: MEM_ID
  //Indicates Slave Memory Depth 
  parameter int MEM_ID = 2**ADDRESS_WIDTH;



endpackage: axi4_globals_pkg

`endif

