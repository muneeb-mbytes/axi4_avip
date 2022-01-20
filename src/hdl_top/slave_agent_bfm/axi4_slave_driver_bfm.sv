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
                                input [3:0]                 arQOS   ,
                                input [3:0]                 arregion,
                                input [3:0]                 aruser  ,
                                input                       arvalid ,
                                output reg                  arready ,

                                //Read Data Channel
                                output reg [3:0]                rid    ,
                                output reg [DATA_WIDTH-1: 0]    rdata  ,
                               // output reg [(DATA_WIDTH/8)-1: 0]rstrb  ,
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
  
  reg [3:0] i = 0;
  reg [3: 0] bid_local; 
  reg [3: 0] rid_local; 
  reg [3:0] j = 0;

  initial begin
    `uvm_info("axi4 slave driver bfm",$sformatf("AXI4 SLAVE DRIVER BFM"),UVM_LOW);
  end

  string name = "AXI4_SLAVE_DRIVER_BFM";

  // Creating Memories for each signal to store each transaction attributes

  reg [	15: 0]	            mem_awid	  [0:19];
  reg [	ADDRESS_WIDTH-1: 0]	mem_waddr	  [0:19];
  reg [	7 : 0]	            mem_wlen	  [0:19];
  reg [	2 : 0]	            mem_wsize	  [0:19];
  reg [ 1	: 0]	            mem_wburst  [0:19];
  reg [ 1	: 0]	            mem_wlock	  [0:19];
  reg [ 3	: 0]	            mem_wcache  [0:19];
  reg [ 2	: 0]	            mem_wprot	  [0:19];
  reg [ 3	: 0]	            mem_wQOS  	[0:19];
  reg [ 3	: 0]	            mem_wregion	[0:19];
  reg [ 3	: 0]	            mem_wuser	  [0:19];

  reg [	15: 0]	            mem_arid	  [0:19];
  reg [	ADDRESS_WIDTH-1: 0]	mem_raddr	  [0:19];
  reg [	7	: 0]	            mem_rlen	  [0:19];
  reg [	2	: 0]	            mem_rsize	  [0:19];
  reg [ 1	: 0]	            mem_rburst  [0:19];
  reg [ 1	: 0]	            mem_rlock	  [0:19];
  reg [ 3	: 0]	            mem_rcache  [0:19];
  reg [ 2	: 0]	            mem_rprot	  [0:19];
  reg [ 3	: 0]	            mem_rQOS   	[0:19];
  reg [ 3	: 0]	            mem_rregion [0:19];
  reg [ 3	: 0]	            mem_ruser	  [0:19];

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
    buser   <= 'bx;
    ruser   <= 'bx;
    arready <= 0;
    bid     <= 'bx;
    bresp   <= 'bx;
    rid     <= 'bx;
    rdata   <= 'bx;
    rresp   <= 'bx;
    @(posedge aresetn);
    `uvm_info(name,$sformatf("SYSTEM RESET DE-ACTIVATED"),UVM_NONE)
  endtask 
  
  //-------------------------------------------------------
  // Task: axi_write_address_phase
  // Sampling the signals that are associated with write_address_channel
  //-------------------------------------------------------

  task axi4_write_address_phase(axi4_write_transfer_char_s data_write_packet);
    @(posedge aclk);
    `uvm_info(name,"INSIDE WRITE_ADDRESS_PHASE",UVM_LOW)

    // Ready can be HIGH even before we start to check 
    // based on wait_cycles variable
    // Can make awready to zero 
    awready <= 0;

    while(awvalid === 0) begin
      @(posedge aclk);
    end

    `uvm_info("SLAVE_DRIVER_WADDR_PHASE", $sformatf("outside of awvalid"), UVM_NONE); 
     
    // Sample the values
    if(awvalid)begin
      mem_awid 	[i]	  = awid  	;	
      `uvm_info("mem_awid",$sformatf("mem_awid[%0d]=%0d",i,mem_awid[i]),UVM_HIGH)
      `uvm_info("mem_awid",$sformatf("awid=%0d",awid),UVM_HIGH)
	   	mem_waddr	[i] 	= awaddr	;
	   	mem_wlen 	[i]	  = awlen	  ;	
	    mem_wsize	[i] 	= awsize	;	
	   	mem_wburst[i] 	= awburst ;	
	   	mem_wlock	[i] 	= awlock	;	
	   	mem_wcache[i] 	= awcache ;	
	   	mem_wprot	[i] 	= awprot	;	
	   	i = i+1                   ;
    end
    for(int k=0;k<$size(mem_awid);k++) begin
      data_write_packet.awid = mem_awid[k]      ;
      data_write_packet.awaddr = mem_waddr[k]   ;
      data_write_packet.awlen = mem_wlen[k]     ;
      data_write_packet.awsize = mem_wsize[k]   ;
      data_write_packet.awburst = mem_wburst[k] ;
      data_write_packet.awlock = mem_wlock[k]   ;
      data_write_packet.awcache = mem_wcache[k] ;
      data_write_packet.awprot = mem_wprot[k]   ;
    end
    `uvm_info(name,$sformatf("struct_pkt_wr_addr_phase = \n %0p",data_write_packet),UVM_HIGH)

   //  data_write_packet.awid = awid;
   //  data_write_packet.awaddr = awaddr;
   //  data_write_packet.awlen = awlen;
   //  data_write_packet.awsize = awsize;
   //  data_write_packet.awburst = awburst;
   //  data_write_packet.awlock = awlock;
   //  data_write_packet.awcache = awcache;
   //  data_write_packet.awprot = awprot;
    
   // based on the wait_cycles we can choose to drive the awready
    `uvm_info(name,$sformatf("Before DRIVING WRITE ADDRS WAIT STATES :: %0d",data_write_packet.no_of_wait_states),UVM_HIGH);
    repeat(data_write_packet.no_of_wait_states)begin
      `uvm_info(name,$sformatf("DRIVING_WRITE_ADDRS_WAIT_STATES :: %0d",data_write_packet.no_of_wait_states),UVM_HIGH);
      @(posedge aclk);
      awready<=0;
    end
    awready <= 1;

  endtask: axi4_write_address_phase 

  //-------------------------------------------------------
  // Task: axi4_write_data_phase
  // This task will sample the write data signals
  //-------------------------------------------------------
  task axi4_write_data_phase (inout axi4_write_transfer_char_s data_write_packet, input axi4_transfer_cfg_s cfg_packet);
  //  @(posedge aclk);
    `uvm_info(name,$sformatf("data_write_packet=\n%p",data_write_packet),UVM_HIGH)
    `uvm_info(name,$sformatf("cfg_packet=\n%p",cfg_packet),UVM_HIGH)
    `uvm_info(name,$sformatf("INSIDE WRITE DATA CHANNEL"),UVM_HIGH)
    
    wready <= 0;

    while(wvalid === 0) begin
      @(posedge aclk);
    end

    `uvm_info("SLAVE_DRIVER_WRITE_DATA_PHASE", $sformatf("outside of wvalid"), UVM_NONE); 

    // based on the wait_cycles we can choose to drive the wready
    `uvm_info(name,$sformatf("Before DRIVING WRITE DATA WAIT STATES :: %0d",data_write_packet.no_of_wait_states),UVM_HIGH);
    repeat(data_write_packet.no_of_wait_states)begin
      `uvm_info(name,$sformatf("DRIVING_WRITE_DATA_WAIT_STATES :: %0d",data_write_packet.no_of_wait_states),UVM_HIGH);
      @(posedge aclk);
      wready<=0;
    end
    wready <= 1 ;
    
 //  for(int s = 0;s<(awlen+1);s = s+1)begin
 //    `uvm_info("SLAVE_DEBUG",$sformatf("mem_length = %0d",awlen),UVM_HIGH)
 //    for(int n = 0;n<(2**awsize);n++)begin
 //      `uvm_info("SLAVE_DEBUG",$sformatf("length = %0d",s),UVM_HIGH)
 //      `uvm_info("SLAVE_DEBUG",$sformatf("mem_size = %0d",awsize),UVM_HIGH)
 //      `uvm_info("SLAVE_DEBUG",$sformatf("mem_strb[%0d] = %0d",n,wstrb[n]),UVM_HIGH)
 //      if(wstrb[n])begin
 //        `uvm_info("slave_wdata",$sformatf("sampled_slave_wdata = %0b",wdata),UVM_HIGH);
 //        data_write_packet.wdata[n]=wdata[8*n+7 -: 8];
 //        `uvm_info("slave_wdata",$sformatf("sampled_slave_wdata[%0d] = %0b",n,data_write_packet.wdata[n]),UVM_HIGH);
 //      end
 //    end
 //  end

    for(int a=0;a<$size(mem_awid);a++)begin
      `uvm_info("SLAVE_DEBUG",$sformatf("mem_awid_size = %0d, mem_awid[%0d] = %0d",$size(mem_awid),a,mem_awid[a]),UVM_HIGH)
      if(mem_wburst[a]==2'b00||mem_wburst[a])begin
        `uvm_info("SLAVE_DEBUG",$sformatf("mem_wburst = %0d",mem_wburst[a]),UVM_HIGH)
        for(int s = 0;s<(mem_wlen[a]+1);s = s+1)begin
          @(posedge aclk);
          `uvm_info("SLAVE_DEBUG",$sformatf("mem_length = %0d",mem_wlen[a]),UVM_HIGH)
          for(int n = 0;n<(2**mem_wsize[a]);n++)begin
            `uvm_info("SLAVE_DEBUG",$sformatf("length = %0d",s),UVM_HIGH)
            `uvm_info("SLAVE_DEBUG",$sformatf("mem_size = %0d",mem_wsize[a]),UVM_HIGH)
            `uvm_info("SLAVE_DEBUG",$sformatf("mem_strb[%0d] = %0d",n,wstrb[n]),UVM_HIGH)
           // if(wstrb[n])begin
              `uvm_info("slave_wdata",$sformatf("sampled_slave_wdata = %0b",wdata),UVM_HIGH);
              data_write_packet.wdata[n]=wdata[8*n+7 -: 8];
              `uvm_info("slave_wdata",$sformatf("sampled_slave_wdata[%0d] = %0b",n,data_write_packet.wdata[n]),UVM_HIGH);
           // end
          end
          if(s == mem_wlen[a]) begin
            data_write_packet.wlast = wlast;
          end
        end
      end
    end

  endtask : axi4_write_data_phase

  //-------------------------------------------------------
  // Task: axi4_write_response_phase
  // This task will drive the write response signals
  //-------------------------------------------------------
  
  task axi4_write_response_phase(axi4_write_transfer_char_s data_write_packet, axi4_transfer_cfg_s struct_cfg,int valid_delay = 2);
    
    int j;
    @(posedge aclk);
    `uvm_info(name,"INSIDE WRITE RESPONSE PHASE",UVM_LOW)
    
    //if(wready && wvalid)begin
      if(std::randomize(bid_local) with {bid_local ==  mem_awid[j];})
        @(posedge aclk);
        bid  = bid_local;
        `uvm_info("bid_debug",$sformatf("mem_awid[%0d]=%0d",j,mem_awid[j]),UVM_HIGH)
        `uvm_info("bid_debug",$sformatf("bid_local=%0d",bid_local),UVM_HIGH)
        bresp <= WRITE_OKAY;
        buser<=data_write_packet.buser;
        bvalid <= 1;
        j++;
          
    //    repeat(valid_delay-1) begin
    //      @(posedge aclk);
    //    end
    //    bvalid = 0;
    // end 
    
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
    `uvm_info(name,$sformatf("INSIDE TO READ ADDRESS CHANNEL"),UVM_HIGH);
    
    // Ready can be HIGH even before we start to check 
    // based on wait_cycles variable
    // Can make arready to zero 
    arready <= 0;

    while(arvalid === 0) begin
      @(posedge aclk);
    end

    `uvm_info("SLAVE_DRIVER_RADDR_PHASE", $sformatf("outside of arvalid"), UVM_NONE); 
     
    // Sample the values
    if(arvalid)begin
      mem_arid 	[j]	  = arid  	;	
      `uvm_info("mem_arid",$sformatf("mem_arid[%0d]=%0d",j,mem_arid[j]),UVM_HIGH)
      `uvm_info("mem_arid",$sformatf("arid=%0d",arid),UVM_HIGH)
	   	mem_raddr	[j] 	= araddr	;
	   	mem_rlen 	[j]	  = arlen	  ;	
	    mem_rsize	[j] 	= arsize	;	
	   	mem_rburst[j] 	= arburst ;	
	   	mem_rlock	[j] 	= arlock	;	
	   	mem_rcache[j] 	= arcache ;	
	   	mem_rprot	[j] 	= arprot	;	
	   	j = j+1                   ;
    end
    for(int p=0;p<$size(mem_awid);p++) begin
      data_read_packet.arid    = mem_arid[p]     ;
      data_read_packet.araddr  = mem_raddr[p]    ;
      data_read_packet.arlen   = mem_rlen[p]     ;
      data_read_packet.arsize  = mem_rsize[p]    ;
      data_read_packet.arburst = mem_rburst[p]   ;
      data_read_packet.arlock  = mem_rlock[p]    ;
      data_read_packet.arcache = mem_rcache[p]   ;
      data_read_packet.arprot  = mem_rprot[p]    ;
    end
    `uvm_info(name,$sformatf("struct_pkt_rd_addr_phase = \n %0p",data_read_packet),UVM_HIGH)

    // based on the wait_cycles we can choose to drive the awready
    `uvm_info(name,$sformatf("Before DRIVING READ ADDRS WAIT STATES :: %0d",data_read_packet.no_of_wait_states),UVM_HIGH);
    repeat(data_read_packet.no_of_wait_states)begin
      `uvm_info(name,$sformatf("DRIVING_READ_ADDRS_WAIT_STATES :: %0d",data_read_packet.no_of_wait_states),UVM_HIGH);
      @(posedge aclk);
      arready<=0;
    end
    arready <= 1;
   
  //  data_read_packet.arid=arid;
  //  data_read_packet.araddr=araddr;
  //  data_read_packet.arlen = arlen;
  //  data_read_packet.arsize = arsize;
  //  data_read_packet.arburst = arburst;
  //  data_read_packet.arlock = arlock;
  //  data_read_packet.arcache = arcache;
  //  data_read_packet.arprot = arprot;

  endtask: axi4_read_address_phase
    
  //-------------------------------------------------------
  // Task: axi4_read_data_channel_task
  // This task will drive the read data signals
  //-------------------------------------------------------
  task axi4_read_data_phase (inout axi4_read_transfer_char_s data_read_packet, input axi4_transfer_cfg_s cfg_packet);
    int j1;
    @(posedge aclk);
    `uvm_info(name,$sformatf("data_read_packet=\n%p",data_read_packet),UVM_HIGH);
    `uvm_info(name,$sformatf("cfg_packet=\n%p",cfg_packet),UVM_HIGH);
    `uvm_info(name,$sformatf("INSIDE READ DATA CHANNEL"),UVM_LOW);
    
    if(std::randomize(rid_local) with {rid_local ==  mem_arid[j1];})
    
      `uvm_info("RDATA_DEBUG",$sformatf("arlen= %0d",arlen),UVM_HIGH);

      for(int i1=0; i1<mem_rlen[j1] + 1; i1++) begin
        @(posedge aclk);
        `uvm_info("RDATA_DEBUG",$sformatf("rid= %0d",rid),UVM_HIGH);
        `uvm_info("RDATA_DEBUG",$sformatf("arlen= %0d",mem_rlen[j1]),UVM_HIGH);
        `uvm_info("RDATA_DEBUG",$sformatf("i1_arlen= %0d",i1),UVM_HIGH);
        rid  <= rid_local;
        for(int l1=0; l1<(2**mem_rsize[j1]); l1++) begin
          `uvm_info("RSIZE_DEBUG",$sformatf("mem_rsize= %0d",mem_rsize[j1]),UVM_HIGH);
          `uvm_info("RSIZE_DEBUG",$sformatf("mem_rsize_l1= %0d",l1),UVM_HIGH);
          rdata[8*l1+7 -: 8]<=data_read_packet.rdata[l1*8+i1];
          `uvm_info("RDATA_DEBUG",$sformatf("RDATA[%0d]=%0h",i1,data_read_packet.rdata[i1]),UVM_HIGH)
          `uvm_info("RDATA_DEBUG",$sformatf("RDATA=%0h",rdata[8*l1+7 -: 8]),UVM_HIGH)
        end
        rresp<=data_read_packet.rresp;
        ruser<=data_read_packet.ruser;
        
        rvalid<=1'b1;
      
      while(rready==0) begin
        @(posedge aclk);
        data_read_packet.wait_count_read_data_channel++;
      end

      if(mem_rlen[j1] == i1)begin
        rlast  <= 1'b1;
        @(posedge aclk);
        rlast <= 1'b0;
        rvalid <= 1'b0;
      end
    end
    j1++;
  
  endtask : axi4_read_data_phase

endinterface : axi4_slave_driver_bfm

`endif
