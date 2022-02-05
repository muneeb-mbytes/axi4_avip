`ifndef AXI4_GLOBALS_PKG_INCLUDED_
`define AXI4_GLOBALS_PKG_INCLUDED_

//--------------------------------------------------------------------------------------------
// Package: axi4_globals_pkg
// Used for storing enums, parameters and defining the structs
//--------------------------------------------------------------------------------------------
package axi4_globals_pkg;

  //-------------------------------------------------------
  // Parameters used in axi4_avip are given below
  //-------------------------------------------------------

  //Parameter: MASTER_AGENT_ACTIVE
  //Used to set the master agent either active or passive
  parameter bit MASTER_AGENT_ACTIVE = 1;

  //Parameter: SLAVE_AGENT_ACTIVE
  //Used to set the slave agent either active or passive
  parameter bit SLAVE_AGENT_ACTIVE = 1;

  //Parameter: NO_OF_MASTERS
  //Used to set number of masters required
  parameter int NO_OF_MASTERS = 1;

  //Parameter: NO_OF_SLAVES
  //Used to set number of slaves required
  parameter int NO_OF_SLAVES = 1;

  //Parameter: ADDRESS_WIDTH
  //Used to set the address width to the address bus
  parameter int ADDRESS_WIDTH = 32;

  //Parameter: DATA_WIDTH
  //Used to set the data width 
  parameter int DATA_WIDTH = 32;

  //Parameter: SLAVE_MEMORY_SIZE
  //Sets the memory size of the slave in KB
  parameter int SLAVE_MEMORY_SIZE = 12;

  //Parameter: SLAVE_MEMORY_GAP
  //Sets the memory gap size of the slave
  parameter int SLAVE_MEMORY_GAP = 2;

  //Parameter: MEMORY_WIDTH
  //Sets the width it can store in each location
  parameter int MEMORY_WIDTH = 8;

  //Variable: MEM_ID
  //Indicates Slave Memory Depth 
  parameter int MEM_ID = 2**ADDRESS_WIDTH;

  //Variable: LENGTH
  //Indicates the length of the address write and read channels
  parameter int LENGTH = 8;

  parameter int OUTSTANDING_FIFO_DEPTH = 16;
  //-------------------------------------------------------
  // Enums used in axi4_avip are given below
  //-------------------------------------------------------
  
  //Enum: awburst_e
  //Used to declare the enum type of write burst type
  typedef enum bit [1:0] {
    WRITE_FIXED    = 2'b00,
    WRITE_INCR     = 2'b01,
    WRITE_WRAP     = 2'b10,
    WRITE_RESERVED = 2'b11
  } awburst_e;

  //Enum: arburst_e
  //Used to declare the enum type of read burst type
  typedef enum bit [1:0] {
    READ_FIXED    = 2'b00,
    READ_INCR     = 2'b01,
    READ_WRAP     = 2'b10,
    READ_RESERVED = 2'b11
  } arburst_e;

  //Enum: transfer_size_e
  //Used to declare enum type for write transfer sizes
  typedef enum bit[2:0]{
    WRITE_1_BYTE    = 3'b000,
    WRITE_2_BYTES   = 3'b001,
    WRITE_4_BYTES   = 3'b010,
    WRITE_8_BYTES   = 3'b011,
    WRITE_16_BYTES  = 3'b100,
    WRITE_32_BYTES  = 3'b101,
    WRITE_64_BYTES  = 3'b110,
    WRITE_128_BYTES = 3'b111
  } awsize_e;

  //Enum: transfer_size_e
  //Used to declare enum type for read transfer sizes
  typedef enum bit[2:0]{
    READ_1_BYTE    = 3'b000,
    READ_2_BYTES   = 3'b001,
    READ_4_BYTES   = 3'b010,
    READ_8_BYTES   = 3'b011,
    READ_16_BYTES  = 3'b100,
    READ_32_BYTES  = 3'b101,
    READ_64_BYTES  = 3'b110,
    READ_128_BYTES = 3'b111
  } arsize_e;

  //Enum: awlock_e
  //Used to declare enum type for write lock access
  typedef enum bit {
    WRITE_NORMAL_ACCESS    = 1'b0,
    WRITE_EXCLUSIVE_ACCESS = 1'b1
  } awlock_e;

  //Enum: arlock_e
  //Used to declare enum type for read lock access
  typedef enum bit {
    READ_NORMAL_ACCESS    = 1'b0,
    READ_EXCLUSIVE_ACCESS = 1'b1
  } arlock_e;

  //Enum: awcache_e
  //Used to declare enum type for write cache access
  typedef enum bit [3:0] {
    WRITE_BUFFERABLE,
    WRITE_MODIFIABLE,
    WRITE_OTHER_ALLOCATE,
    WRITE_ALLOCATE
  } awcache_e;

  //Enum: arcache_e
  //Used to declare enum type for read cache access
  typedef enum bit [3:0] {
    READ_BUFFERABLE,
    READ_MODIFIABLE,
    READ_OTHER_ALLOCATE,
    READ_ALLOCATE
  } arcache_e;

  //Enum: endian_e
  //Used to declare enum type for the endians
  typedef enum bit {
    BIG_ENDIAN    = 1'b0,
    LITTLE_ENDIAN = 1'b1
  } endian_e;

  //Enum: awprot_e 
  //Used to declare enum type of write protection of the transaction
  typedef enum bit [2:0] {
    WRITE_NORMAL_SECURE_DATA               = 3'b000,
    WRITE_NORMAL_SECURE_INSTRUCTION        = 3'b001,
    WRITE_NORMAL_NONSECURE_DATA            = 3'b010,
    WRITE_NORMAL_NONSECURE_INSTRUCTION     = 3'b011,
    WRITE_PRIVILEGED_SECURE_DATA           = 3'b100,
    WRITE_PRIVILEGED_SECURE_INSTRUCTION    = 3'b101,
    WRITE_PRIVILEGED_NONSECURE_DATA        = 3'b110,
    WRITE_PRIVILEGED_NONSECURE_INSTRUCTION = 3'b111
  } awprot_e;

  //Enum: arprot_e 
  //Used to declare enum type of read protection of the transaction
  typedef enum bit [2:0] {
    READ_NORMAL_SECURE_DATA               = 3'b000,
    READ_NORMAL_SECURE_INSTRUCTION        = 3'b001,
    READ_NORMAL_NONSECURE_DATA            = 3'b010,
    READ_NORMAL_NONSECURE_INSTRUCTION     = 3'b011,
    READ_PRIVILEGED_SECURE_DATA           = 3'b100,
    READ_PRIVILEGED_SECURE_INSTRUCTION    = 3'b101,
    READ_PRIVILEGED_NONSECURE_DATA        = 3'b110,
    READ_PRIVILEGED_NONSECURE_INSTRUCTION = 3'b111
  } arprot_e;

  //Enum: bresp_e
  //Used to declare the enum type of write response
  typedef enum bit [1:0] {
    WRITE_OKAY   = 2'b00,
    WRITE_EXOKAY = 2'b01,
    WRITE_SLVERR = 2'b10,
    WRITE_DECERR = 2'b11
  } bresp_e;

  //Enum: rresp_e
  //Used to declare the enum type of read response
  typedef enum bit [1:0] {
    READ_OKAY   = 2'b00,
    READ_EXOKAY = 2'b01,
    READ_SLVERR = 2'b10,
    READ_DECERR = 2'b11
  } rresp_e;

  //Enum: tx_type
  //Used to declare the type of transaction done
  typedef enum bit {
    WRITE = 1,
    READ  = 0
  } tx_type_e;

  //Enum : transfer_type_e
  //Used to the determine the type of the transfer
  typedef enum bit[1:0]{
    BLOCKING_WRITE      = 2'b00, 
    BLOCKING_READ       = 2'b01, 
    NON_BLOCKING_WRITE  = 2'b10, 
    NON_BLOCKING_READ   = 2'b11 
  } transfer_type_e;

  //-------------------------------------------------------
  // Structs used in axi_avip are given below
  //-------------------------------------------------------
  
  //Struct: axi4_w_transfer_char_s
  //This struct datatype consists of all write signals which are used for seq item conversion
  typedef struct {
    //Write_address_channel
    bit [3:0]               awid;
    bit [ADDRESS_WIDTH-1:0] awaddr;
    bit [7:0]               awlen;
    bit [2:0]               awsize;
    bit [1:0]               awburst;
    bit                     awlock;
    bit [3:0]               awcache;
    bit [3:0]               awqos;
    bit [3:0]               awregion;
    bit                     awuser;
    bit [2:0]               awprot;
    bit                     awvalid;
    bit	                    awready;
    //Write_data_channel
    bit [2**LENGTH:0][DATA_WIDTH-1:0]     wdata;
    bit [2**LENGTH:0][(DATA_WIDTH/8)-1:0] wstrb;
    bit                     [2**LENGTH:0] wuser;
    bit                                   wlast;

    //Write Response Channel
    bit [3:0] bid;
    bit [1:0] bresp;
    bit       bvalid;
    bit       buser;

    int wait_count_write_address_channel;
    int wait_count_write_data_channel;
    int wait_count_write_response_channel;
    
    int outstanding_write_tx;
    int no_of_wait_states;
    bit tx_type; 
  } axi4_write_transfer_char_s; 

  //Struct: axi4_r_transfer_char_s
  //This struct datatype consists of all read signals which are used for seq item conversion
  typedef struct {
    //Read Address Channel
    bit               [3:0] arid;
    bit [ADDRESS_WIDTH-1:0] araddr;
    bit               [7:0] arlen;
    bit               [2:0] arsize;
    bit               [1:0] arburst;
    bit               [3:0] arcache;
    bit               [2:0] arprot;
    bit               [3:0] arqos;
    bit               [3:0] arregion;
    bit               [3:0] aruser;
    bit                     arlock;
    //Read Data Channel
    bit                         [3:0] rid;
    bit [2**LENGTH:0][DATA_WIDTH-1:0] rdata;
    bit            [2**LENGTH:0][1:0] rresp; 
    bit            [2**LENGTH:0][3:0] ruser;
    bit                               rvalid;
    bit                               rlast;
    
    int wait_count_read_address_channel;
    int wait_count_read_data_channel;
    
    int outstanding_read_tx;
    int no_of_wait_states;
    bit tx_type; 
  } axi4_read_transfer_char_s;

  //Struct: axi4_cfg_char_s
  //This struct datatype consists of all configurations which are used for seq item conversion
  typedef struct {
    bit [ADDRESS_WIDTH-1:0] min_address;
    bit [ADDRESS_WIDTH-1:0] max_address;
    
    int wait_count_read_address_channel;
    int wait_count_read_data_channel;
    int wait_count_write_address_channel;
    int wait_count_write_data_channel;
    int wait_count_write_response_channel;
    
    int outstanding_write_tx;
    int outstanding_read_tx;
  } axi4_transfer_cfg_s;

endpackage : axi4_globals_pkg

`endif

