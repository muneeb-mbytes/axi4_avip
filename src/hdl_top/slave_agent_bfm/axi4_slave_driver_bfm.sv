`ifndef AXI4_SLAVE_DRIVER_BFM_INCLUDED_
`define AXI4_SLAVE_DRIVER_BFM_INCLUDED_

//--------------------------------------------------------------------------------------------
//Interface : axi4_slave_driver_bfm
//Used as the HDL driver for axi4
//It connects with the HVL driver_proxy for driving the stimulus
//--------------------------------------------------------------------------------------------
import axi4_globals_pkg::*;
interface axi4_slave_driver_bfm(input                     aclk    , 
                                input                     aresetn ,
                                //Write_address_channel
                                input [3:0]               awid    ,
                                input [ADDRESS_WIDTH-1:0] awaddr  ,
                                input [3: 0]              awlen   ,
                                input [2: 0]              awsize  ,
                                input [1: 0]              awburst ,
                                input [1: 0]              awlock  ,
                                input [3: 0]              awcache ,
                                input [2: 0]              awprot  ,
                                input                     awvalid ,
                                output reg	              awready ,

                                //Write_data_channel
                                input [DATA_WIDTH-1: 0]     wdata  ,
                                input [(DATA_WIDTH/8)-1: 0] wstrb  ,
                                input                       wlast  ,
                                input [3: 0]                wuser  ,
                                input                       wvalid ,
                                output reg	                wready ,

                                //Write Response Channel
                                output reg [3:0]            bid    ,
                                output reg [1:0]            bresp  ,
                                output reg [3:0]            buser  ,
                                output reg                  bvalid ,
                                input		                    bready ,

                                //Read Address Channel
                                input [3: 0]                arid    ,
                                input [ADDRESS_WIDTH-1: 0]  araddr  ,
                                input [7:0]                 arlen   ,
                                input [2:0]                 arsize  ,
                                input [1:0]                 arburst ,
                                input [1:0]                 arlock  ,
                                input [3:0]                 arcache ,
                                input [2:0]                 arprot  ,
                                input [3:0]                 arqos   ,
                                input [3:0]                 arregion,
                                input [3:0]                 aruser  ,
                                input                       arvalid ,
                                output reg                  arready ,

                                //Read Data Channel
                                output reg [3:0]                rid    ,
                                output reg [DATA_WIDTH-1: 0]    rdata  ,
                                output reg [1:0]                rresp  ,
                                output reg                      rlast  ,
                                output reg [3:0]                ruser  ,
                                output reg                      rvalid ,
                                input		                        rready  
                              ); 
                              
  //-------------------------------------------------------
  // Importing UVM Package 
  //-------------------------------------------------------
  import uvm_pkg::*;
  `include "uvm_macros.svh" 

  //-------------------------------------------------------
  // Importing axi4 slave driver proxy
  //-------------------------------------------------------
  import axi4_slave_pkg::axi4_slave_driver_proxy;

  //Variable : axi4_slave_driver_proxy_h
  //Creating the handle for proxy driver
  axi4_slave_driver_proxy axi4_slave_drv_proxy_h;
  
  reg [3: 0] i = 0;
  reg [3: 0] j = 0;
  reg [7: 0] a = 0;

  initial begin
    `uvm_info("axi4 slave driver bfm",$sformatf("AXI4 SLAVE DRIVER BFM"),UVM_LOW);
  end

  string name = "AXI4_SLAVE_DRIVER_BFM";

  // Creating Memories for each signal to store each transaction attributes

  reg [	15: 0]	            mem_awid	  [OUTSTANDING_FIFO_DEPTH];
  reg [	ADDRESS_WIDTH-1: 0]	mem_waddr	  [OUTSTANDING_FIFO_DEPTH];
  reg [	7 : 0]	            mem_wlen	  [OUTSTANDING_FIFO_DEPTH];
  reg [	2 : 0]	            mem_wsize	  [OUTSTANDING_FIFO_DEPTH];
  reg [ 1	: 0]	            mem_wburst  [OUTSTANDING_FIFO_DEPTH];
  bit                       mem_wlast   [OUTSTANDING_FIFO_DEPTH];
  
  reg [	15: 0]	            mem_arid	  [OUTSTANDING_FIFO_DEPTH];
  reg [	ADDRESS_WIDTH-1: 0]	mem_raddr	  [OUTSTANDING_FIFO_DEPTH];
  reg [	7	: 0]	            mem_rlen	  [OUTSTANDING_FIFO_DEPTH];
  reg [	2	: 0]	            mem_rsize	  [OUTSTANDING_FIFO_DEPTH];
  reg [ 1	: 0]	            mem_rburst  [OUTSTANDING_FIFO_DEPTH];
  
  //-------------------------------------------------------
  // Task: wait_for_system_reset
  // Waiting for the system reset to be active low
  //-------------------------------------------------------

  task wait_for_system_reset();
    @(negedge aresetn);
    `uvm_info(name,$sformatf("SYSTEM RESET ACTIVATED"),UVM_NONE)
    awready <= 0;
    wready  <= 0;
    rvalid  <= 0;
    rlast   <= 0;
    bvalid  <= 0;
    arready <= 0;
    bid     <= 'bx;
    bresp   <= 'bx;
    buser   <= 'bx;
    rid     <= 'bx;
    rdata   <= 'bx;
    rresp   <= 'bx;
    ruser   <= 'bx;
    @(posedge aresetn);
    `uvm_info(name,$sformatf("SYSTEM RESET DE-ACTIVATED"),UVM_NONE)
  endtask 
  
  //-------------------------------------------------------
  // Task: axi_write_address_phase
  // Sampling the signals that are associated with write_address_channel
  //-------------------------------------------------------

  task axi4_write_address_phase(inout axi4_write_transfer_char_s data_write_packet);
    @(posedge aclk);
    `uvm_info(name,"INSIDE WRITE_ADDRESS_PHASE",UVM_LOW)

    // Ready can be HIGH even before we start to check 
    // based on wait_cycles variable
    // Can make awready to zero 
    awready <= 0;

    do begin
      @(posedge aclk);
    end while(awvalid===0);

    `uvm_info("SLAVE_DRIVER_WADDR_PHASE", $sformatf("outside of awvalid"), UVM_MEDIUM); 
     
   // Sample the values
   
   mem_awid 	[i]	  = awid  	;	
	 mem_waddr	[i] 	= awaddr	;
	 mem_wlen 	[i]	  = awlen	  ;	
	 mem_wsize	[i] 	= awsize	;	
	 mem_wburst [i]   = awburst ;	
   
   data_write_packet.awid    = mem_awid   [i] ;
   data_write_packet.awaddr  = mem_waddr  [i] ;
   data_write_packet.awlen   = mem_wlen   [i] ;
   data_write_packet.awsize  = mem_wsize  [i] ;
   data_write_packet.awburst = mem_wburst [i] ;
   
   i = i+1                   ;
    
   `uvm_info("mem_awid",$sformatf("mem_awid[%0d]=%0d",i,mem_awid[i]),UVM_HIGH)
   `uvm_info("mem_awid",$sformatf("awid=%0d",awid),UVM_HIGH)

   `uvm_info("struct_pkt_debug",$sformatf("struct_pkt_wr_addr_phase = \n %0p",data_write_packet),UVM_HIGH)

   // based on the wait_cycles we can choose to drive the awready
    `uvm_info(name,$sformatf("Before DRIVING WRITE ADDRS WAIT STATES :: %0d",data_write_packet.no_of_wait_states),UVM_HIGH);
    repeat(data_write_packet.no_of_wait_states)begin
      `uvm_info(name,$sformatf("DRIVING_WRITE_ADDRS_WAIT_STATES :: %0d",data_write_packet.no_of_wait_states),UVM_HIGH);
      @(posedge aclk);
      awready<=0;
    end
    awready <= 1;

    if(i == OUTSTANDING_FIFO_DEPTH)begin
      `uvm_info(name,$sformatf("REACHED OUTSTANDING_FIFO_DEPTH"),UVM_MEDIUM)
      @(posedge aclk);
      awready <= 0;
    end

  endtask: axi4_write_address_phase 

  //-------------------------------------------------------
  // Task: axi4_write_data_phase
  // This task will sample the write data signals
  //-------------------------------------------------------
  task axi4_write_data_phase (inout axi4_write_transfer_char_s data_write_packet, input axi4_transfer_cfg_s cfg_packet);
    `uvm_info(name,$sformatf("data_write_packet=\n%p",data_write_packet),UVM_HIGH)
    `uvm_info(name,$sformatf("cfg_packet=\n%p",cfg_packet),UVM_HIGH)
    `uvm_info(name,$sformatf("INSIDE WRITE DATA CHANNEL"),UVM_HIGH)
    
    wready <= 0;
    
    do begin
      @(posedge aclk);
    end while(wvalid===0);

    `uvm_info("SLAVE_DRIVER_WRITE_DATA_PHASE", $sformatf("outside of wvalid"), UVM_MEDIUM); 

   // based on the wait_cycles we can choose to drive the wready
    `uvm_info("SLAVE_BFM_WDATA_PHASE",$sformatf("Before DRIVING WRITE DATA WAIT STATES :: %0d",data_write_packet.no_of_wait_states),UVM_HIGH);
    repeat(data_write_packet.no_of_wait_states)begin
      `uvm_info(name,$sformatf("DRIVING_WRITE_DATA_WAIT_STATES :: %0d",data_write_packet.no_of_wait_states),UVM_HIGH);
      @(posedge aclk);
      wready<=0;
    end

    wready <= 1 ;
    
    for(int s = 0;s<(mem_wlen[a]+1);s = s+1)begin
      @(posedge aclk);
      `uvm_info("SLAVE_DEBUG",$sformatf("mem_length = %0d",mem_wlen[a]),UVM_HIGH)
       data_write_packet.wdata[s]=wdata;
       `uvm_info("slave_wdata",$sformatf("sampled_slave_wdata[%0d] = %0h",s,data_write_packet.wdata[s]),UVM_HIGH);
       data_write_packet.wstrb[s]=wstrb;
       `uvm_info("slave_wstrb",$sformatf("sampled_slave_wstrb[%0d] = %0d",s,data_write_packet.wstrb[s]),UVM_HIGH);
        if(s == mem_wlen[a]) begin
          mem_wlast[a] <= wlast;
          data_write_packet.wlast = wlast;
          if(!data_write_packet.wlast)begin
            @(posedge aclk);
            wready<=0;
            break;
          end
          `uvm_info("slave_wlast",$sformatf("slave_wlast = %0b",wlast),UVM_HIGH);
          `uvm_info("slave_wlast",$sformatf("sampled_slave_wlast = %0b",data_write_packet.wlast),UVM_HIGH);
        end
      end
      `uvm_info(name,$sformatf("OUTSIDE WRITE DATA CHANNEL"),UVM_HIGH)
      a++;

      @(posedge aclk);
      wready <= 0;
   
      //   for(int n = 0;n<(2**mem_wsize[a]);n++)begin
      //     `uvm_info("SLAVE_DEBUG",$sformatf("length = %0d",s),UVM_HIGH)
      //     `uvm_info("SLAVE_DEBUG",$sformatf("mem_size = %0d",mem_wsize[a]),UVM_HIGH)
      //     `uvm_info("SLAVE_DEBUG",$sformatf("mem_strb[%0d] = %0d",n,wstrb[n]),UVM_HIGH)
      //     if(wstrb[n])begin
      //       `uvm_info("slave_wdata",$sformatf("sampled_slave_wdata = %0d",wdata),UVM_HIGH);
      //       data_write_packet.wdata[s][n*8+:8]=wdata[8*n+7 -: 8];
      //       `uvm_info("slave_wdata",$sformatf("sampled_slave_wdata[%0d] = %0d",n,data_write_packet.wdata[s][n*8+:8]),UVM_HIGH);
      //       `uvm_info("slave_wdata",$sformatf("sampled_slave_wdata = %0d",wdata[8*n+7 -: 8]),UVM_HIGH);
      //     end
      //   end
  
  endtask : axi4_write_data_phase

  //-------------------------------------------------------
  // Task: axi4_write_response_phase
  // This task will drive the write response signals
  //-------------------------------------------------------
  
  task axi4_write_response_phase(inout axi4_write_transfer_char_s data_write_packet, axi4_transfer_cfg_s struct_cfg);
    
    int j;
    @(posedge aclk);
    data_write_packet.bid <= mem_awid[j]; 
    `uvm_info("DEBUG_BRESP",$sformatf("BID = %0d",data_write_packet.bid),UVM_HIGH)
    `uvm_info(name,"INSIDE WRITE_RESPONSE_PHASE",UVM_LOW)
    
    bid  <= mem_awid[j];
    `uvm_info("DEBUG_BRESP_WLAST",$sformatf("wlast = %0d",mem_wlast[j]),UVM_HIGH)
    if(mem_wlast[j]==1) begin
      bresp <= WRITE_OKAY;
      data_write_packet.bresp <= bresp;
    end
    else begin
      data_write_packet.bresp <= WRITE_SLVERR;
      bresp <= WRITE_SLVERR;
    end
      
    buser<=data_write_packet.buser;
    bvalid <= 1;
    j++;
    `uvm_info("DEBUG_BRESP",$sformatf("BID = %0d",bid),UVM_HIGH)
    
    while(bready === 0) begin
      @(posedge aclk);
      data_write_packet.wait_count_write_response_channel++;
      `uvm_info(name,$sformatf("inside_detect_bready = %0d",bready),UVM_HIGH)
    end
    `uvm_info(name,$sformatf("After_loop_of_Detecting_bready = %0d",bready),UVM_HIGH)
    bvalid <= 1'b0;
  
  endtask : axi4_write_response_phase

  //-------------------------------------------------------
  // Task: axi4_read_address_phase
  // This task will sample the read address signals
  //-------------------------------------------------------
  task axi4_read_address_phase (inout axi4_read_transfer_char_s data_read_packet, input axi4_transfer_cfg_s cfg_packet);
    @(posedge aclk);
    `uvm_info(name,$sformatf("data_read_packet=\n%p",data_read_packet),UVM_HIGH);
    `uvm_info(name,$sformatf("cfg_packet=\n%p",cfg_packet),UVM_HIGH);
    `uvm_info(name,$sformatf("INSIDE READ ADDRESS CHANNEL"),UVM_HIGH);
    
    // Ready can be HIGH even before we start to check 
    // based on wait_cycles variable
    // Can make arready to zero 
     arready <= 0;

    while(arvalid === 0) begin
      @(posedge aclk);
    end
   
    repeat(data_read_packet.no_of_wait_states)begin
      `uvm_info(name,$sformatf("DRIVING_READ_ADDRS_WAIT_STATES :: %0d",data_read_packet.no_of_wait_states),UVM_HIGH);
      @(posedge aclk);
      arready<=0;
    end

    `uvm_info("SLAVE_DRIVER_RADDR_PHASE", $sformatf("outside of arvalid"), UVM_NONE); 
    
    // Sample the values
    mem_arid 	[j]	  = arid  	;	
	  mem_raddr	[j] 	= araddr	;
	  mem_rlen 	[j]	  = arlen	  ;	
	  mem_rsize	[j] 	= arsize	;	
	  mem_rburst[j] 	= arburst ;	
    arready        <= 1       ;

    data_read_packet.arid    = mem_arid[j]     ;
    data_read_packet.araddr  = mem_raddr[j]    ;
    data_read_packet.arlen   = mem_rlen[j]     ;
    data_read_packet.arsize  = mem_rsize[j]    ;
    data_read_packet.arburst = mem_rburst[j]   ;
	  j = j+1                                    ;

    `uvm_info("mem_arid",$sformatf("mem_arid[%0d]=%0d",j,mem_arid[j]),UVM_HIGH)
    `uvm_info("mem_arid",$sformatf("arid=%0d",arid),UVM_HIGH)
    `uvm_info(name,$sformatf("struct_pkt_rd_addr_phase = \n %0p",data_read_packet),UVM_HIGH)
    
    @(posedge aclk);
    arready <= 0;
  
  endtask: axi4_read_address_phase
    
  //-------------------------------------------------------
  // Task: axi4_read_data_channel_task
  // This task will drive the read data signals
  //-------------------------------------------------------
  task axi4_read_data_phase (inout axi4_read_transfer_char_s data_read_packet, input axi4_transfer_cfg_s cfg_packet);
    int j1;
    @(posedge aclk);
    data_read_packet.rid <= mem_arid[j1];
    `uvm_info("RDATA_DEBUG",$sformatf("data_packet_rid= %0d",data_read_packet.rid),UVM_HIGH);
    `uvm_info("RDATA_DEBUG",$sformatf("data_packet_rid= %0d",mem_arid[j1]),UVM_HIGH);
    `uvm_info(name,$sformatf("INSIDE READ DATA CHANNEL"),UVM_LOW);
    
    for(int i1=0; i1<mem_rlen[j1] + 1; i1++) begin
      `uvm_info("RDATA_DEBUG",$sformatf("rid= %0d",rid),UVM_HIGH);
      `uvm_info("RDATA_DEBUG",$sformatf("arlen= %0d",mem_rlen[j1]),UVM_HIGH);
      `uvm_info("RDATA_DEBUG",$sformatf("i1_arlen= %0d",i1),UVM_HIGH);
      
      rid  <= mem_arid[j1];
      for(int l1=0; l1<(2**mem_rsize[j1]); l1++) begin
        `uvm_info("RSIZE_DEBUG",$sformatf("mem_rsize= %0d",mem_rsize[j1]),UVM_HIGH);
        `uvm_info("RSIZE_DEBUG",$sformatf("mem_rsize_l1= %0d",l1),UVM_HIGH);
        rdata[8*l1+7 -: 8]<=data_read_packet.rdata[l1*8+i1];
        `uvm_info("RDATA_DEBUG",$sformatf("RDATA[%0d]=%0h",i1,data_read_packet.rdata[i1]),UVM_HIGH)
        `uvm_info("RDATA_DEBUG",$sformatf("RDATA=%0h",rdata[8*l1+7 -: 8]),UVM_HIGH)
      end
      //rdata<=data_read_packet.rdata[i1];
      //`uvm_info("SLAVE_RDATA_DEBUG",$sformatf("rdata= %0d",rdata),UVM_HIGH);
      
      rresp<=data_read_packet.rresp;
      ruser<=data_read_packet.ruser;
      rvalid<=1'b1;
      
      if((mem_rlen[j1]) == i1)begin
        rlast  <= 1'b1;
        @(posedge aclk);
        rlast <= 1'b0;
        rvalid <= 1'b0;
      end
      
      do begin
        @(posedge aclk);
      end while(rready===0);
    end
    j1++;
    
       
  endtask : axi4_read_data_phase

endinterface : axi4_slave_driver_bfm

`endif
