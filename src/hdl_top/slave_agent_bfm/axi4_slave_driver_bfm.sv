`ifndef AXI4_SLAVE_DRIVER_BFM_INCLUDED_
`define AXI4_SLAVE_DRIVER_BFM_INCLUDED_

//--------------------------------------------------------------------------------------------
//Interface : axi4_slave_driver_bfm
//Used as the HDL driver for axi4
//It connects with the HVL driver_proxy for driving the stimulus
//--------------------------------------------------------------------------------------------
import axi4_globals_pkg::*;
interface axi4_slave_driver_bfm(input                          aclk    , 
                                input                          aresetn ,
                                //Write_address_channel
                                input [3:0]                    awid    ,
                                input [ADDRESS_WIDTH-1:0]      awaddr  ,
                                input [3: 0]                   awlen   ,
                                input [2: 0]                   awsize  ,
                                input [1: 0]                   awburst ,
                                input [1: 0]                   awlock  ,
                                input [3: 0]                   awcache ,
                                input [2: 0]                   awprot  ,
                                input                          awvalid ,
                                output reg	                   awready ,

                                //Write_data_channel
                                input [DATA_WIDTH-1: 0]         wdata  ,
                                input [(DATA_WIDTH/8)-1: 0]     wstrb  ,
                                input                           wlast  ,
                                input [3: 0]                    wuser  ,
                                input                           wvalid ,
                                output reg	                    wready ,

                                //Write Response Channel
                                output reg [3:0]                bid    ,
                                output reg [1:0]                bresp  ,
                                output reg [3:0]                buser  ,
                                output reg                      bvalid ,
                                input		                        bready ,

                                //Read Address Channel
                                input [3: 0]                    arid    ,
                                input [ADDRESS_WIDTH-1: 0]      araddr  ,
                                input [7:0]                     arlen   ,
                                input [2:0]                     arsize  ,
                                input [1:0]                     arburst ,
                                input [1:0]                     arlock  ,
                                input [3:0]                     arcache ,
                                input [2:0]                     arprot  ,
                                input [3:0]                     arQOS   ,
                                input [3:0]                     arregion,
                                input [3:0]                     aruser  ,
                                input                           arvalid ,
                                output reg                      arready ,

                                //Read Data Channel
                                output reg [3:0]                 rid     ,
                                output reg [DATA_WIDTH-1: 0]     rdata   ,
                                output reg [(DATA_WIDTH/8)-1: 0] rstrb   ,
                                output reg [1:0]                 rresp   ,
                                output reg                       rlast   ,
                                output reg [3:0]                 ruser   ,
                                output reg                       rvalid  ,
                                input		                         rready  
                              ); 
                              
  // Internal signals
  // reg                            sys_clk_i      ;  
  // reg      [ ADDRESS_WIDTH-1: 0] sys_addr_o     ;  
  // reg      [ 8-1: 0]             sys_wdata_o    ;  
  // reg      [ AXI_SW-1: 0]        sys_sel_o      ;  
  // reg                            sys_wen_o      ;  
  // reg                            sys_ren_o      ;  
  // reg      [ 8-1: 0]             sys_rdata_i    ; 

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
  //reg [3:0] a1 = 0;
  //integer wrap = 0,start_bound = 0,end_bound = 0,l_t1 = 0,l_t2 = 0;

  initial begin
    `uvm_info("axi4 slave driver bfm",$sformatf("AXI4 SLAVE DRIVER BFM"),UVM_LOW);
  end

  string name = "AXI4_SLAVE_DRIVER_BFM";

  // Creating Memories for each signal to store each transaction attributes

  reg [	15: 0]	            mem_awid	  [20];
  reg [	ADDRESS_WIDTH-1: 0]	mem_waddr	  [20];
  reg [	7:0]	              mem_wlen	  [256] ;
  reg [	2:0]	              mem_wsize	  [20];
  reg [ 1	: 0]	            mem_wburst  [20];
  reg [ 1	: 0]	            mem_wlock	  [20];
  reg [ 3	: 0]	            mem_wcache  [20];
  reg [ 2	: 0]	            mem_wprot	  [20];
  reg [ 3	: 0]	            mem_wQOS  	[20];
  reg [ 3	: 0]	            mem_wregion	[20];
  reg [ 3	: 0]	            mem_wuser	  [20];

  reg [	15: 0]	            mem_rid		  [20];
  reg [	ADDRESS_WIDTH-1: 0]	mem_raddr	  [20];
  reg [	7	: 0]	            mem_rlen	  [256];
  reg [	2	: 0]	            mem_rsize	  [20];
  reg [ 1	: 0]	            mem_rburst  [20];
  reg [ 1	: 0]	            mem_rlock	  [20];
  reg [ 3	: 0]	            mem_rcache  [20];
  reg [ 2	: 0]	            mem_rprot	  [20];
  reg [ 3	: 0]	            mem_rQOS   	[20];
  reg [ 3	: 0]	            mem_rregion [20];
  reg [ 3	: 0]	            mem_ruser	  [20];

  //-------------------------------------------------------
  // Task: wait_for_system_reset
  // Waiting for the system reset to be active low
  //-------------------------------------------------------

  task wait_for_system_reset();
    @(posedge aclk);
    if(!aresetn) begin
      `uvm_info(name,$sformatf("SYSTEM RESET ACTIVATED"),UVM_NONE)
    end
    else begin
      `uvm_info(name,$sformatf("SYSTEM RESET DE-ACTIVATED"),UVM_NONE)
    end
  endtask 
  
  //-------------------------------------------------------
  // Task: detect_write_address_wait_state
  // Waiting for the awready to set to high to setup the address,
  // in write address channel
  //-------------------------------------------------------
  task detect_write_address_wait_state(inout axi4_write_transfer_char_s data_write_packet);
    @(posedge aclk);
    `uvm_info(name,$sformatf("DETECT_WRITE_ADDRESS_WAIT_STATE"),UVM_HIGH)

    while(awready==0) begin
      @(posedge aclk);
      data_write_packet.wait_count_write_address_channel++;
    end
  endtask : detect_write_address_wait_state
  
  //-------------------------------------------------------
  // Task: detect_write_data_wait_state
  // Waiting for the wready to set to high to transfer the data packet,
  // in write address channel
  //-------------------------------------------------------
  task detect_write_data_wait_state(inout axi4_write_transfer_char_s data_write_packet);
    @(posedge aclk);
    `uvm_info(name,$sformatf("DETECT_WRITE_DATA_WAIT_STATE"),UVM_HIGH)

    while(wready==0) begin
      @(posedge aclk);
      data_write_packet.wait_count_write_data_channel++;
    end
  endtask : detect_write_data_wait_state
  
  //-------------------------------------------------------
  // Task: detect_read_address_wait_state
  // Waiting for the arready to set to high to setup the address,
  // in read address channel
  //-------------------------------------------------------
  task detect_read_address_wait_state(inout axi4_read_transfer_char_s data_read_packet);
    @(posedge aclk);
    `uvm_info(name,$sformatf("DETECT_READ_ADDRESS_WAIT_STATE"),UVM_HIGH)

    while(arready==0) begin
      @(posedge aclk);
      data_read_packet.wait_count_read_address_channel++;
    end
  endtask : detect_read_address_wait_state
  
  //-------------------------------------------------------
  // Task: detect_read_data_wait_state
  // Waiting for the rready to set to high for data transfer and 
  // to get the response back, in read data channel
  //-------------------------------------------------------
  task detect_read_data_wait_state(inout axi4_read_transfer_char_s data_read_packet);
    @(posedge aclk);
    `uvm_info(name,$sformatf("DETECT_READ_DATA_WAIT_STATE"),UVM_HIGH)

    while(rready==0) begin
      @(posedge aclk);
      data_read_packet.wait_count_read_data_channel++;
    end
  endtask : detect_read_data_wait_state
  
  //-------------------------------------------------------
  // Task: axi_write_address_phase
  // Sampling the signals that are associated with write_address_channel
  //-------------------------------------------------------

  task axi4_write_address_phase(axi4_write_transfer_char_s data_write_packet);
   // @(posedge aclk)begin
      `uvm_info(name,"INSIDE WRITE_ADDRESS_PHASE",UVM_LOW)
      if(!aresetn)begin
      end
      else begin
        if(awvalid)begin
        //  awready=1;
          mem_awid 	[i]	  <= awid  	;	
          //data_write_packet.awid = awid   ;
			    mem_waddr	[i] 	<= awaddr	;
          //data_write_packet.awaddr = awaddr;
			    mem_wlen 	[i]	  <= awlen	;	
          //data_write_packet.awlen = awlen;
			    mem_wsize	[i] 	<= awsize	;	
          //data_write_packet.awsize = awsize;
			    mem_wburst[i] 	<= awburst;	
          //data_write_packet.awburst = awburst;
			    mem_wlock	[i] 	<= awlock	;	
          //data_write_packet.awlock = awlock;
			    mem_wcache[i] 	<= awcache;	
          //data_write_packet.awcache = awcache;
			    mem_wprot	[i] 	<= awprot	;	
          //data_write_packet.awprot = awprot;
			    i <= i+1;
          for(int k=0;k<$size(mem_awid);k++) begin
            data_write_packet.awid = mem_awid[k];
            data_write_packet.awaddr = mem_waddr[k];
            data_write_packet.awlen = mem_wlen[k];
            data_write_packet.awsize = mem_wsize[k];
            data_write_packet.awburst = mem_wburst[k];
            data_write_packet.awlock = mem_wlock[k];
            data_write_packet.awcache = mem_wcache[k];
            data_write_packet.awprot = mem_wprot[k];
//  data_write_packet.awid = awid;
//  data_write_packet.awaddr = awaddr;
//  data_write_packet.awlen = awlen;
//  data_write_packet.awsize = awsize;
//  data_write_packet.awburst = awburst;
//  data_write_packet.awlock = awlock;
//  data_write_packet.awcache = awcache;
//  data_write_packet.awprot = awprot;
    `uvm_info(name,$sformatf("struct_pkt_wr_addr_phase = \n %0p",data_write_packet),UVM_HIGH)
  end
  end
  end
  //end

 // if (awready==0) begin
 //   detect_write_address_wait_state(data_write_packet);
 // end
    repeat(data_write_packet.no_of_wait_states)begin
      `uvm_info(name,$sformatf("DRIVING WAIT STATES :: %0d",data_write_packet.no_of_wait_states),UVM_HIGH);
      @(posedge aclk);
      awready<=0;
    end
   assign awready = awvalid;  //awready <= 1;

    data_write_packet.awready=awready;
  endtask

  //-------------------------------------------------------
  // Task: axi4_write_data_phase
  // This task will sample the write data signals
  //-------------------------------------------------------
 // task axi4_write_data_phase (inout axi4_write_transfer_char_s data_write_packet, input axi4_transfer_cfg_s cfg_packet);
 //   `uvm_info(name,$sformatf("data_write_packet=\n%p",data_write_packet),UVM_HIGH)
 //   `uvm_info(name,$sformatf("cfg_packet=\n%p",cfg_packet),UVM_HIGH)
 //   `uvm_info(name,$sformatf("DRIVE TO WRITE DATA CHANNEL"),UVM_HIGH)
 //   
 // if(wvalid)begin
 //   wready=1;
 //   data_write_packet.wdata=wdata;
 //   data_write_packet.wstrb=wstrb;
 // end
 // if (wready==0) begin
 //     detect_write_data_wait_state(data_write_packet);
 //   end
 // // else begin
 // //  wready=0;
 // // end

 //   //write else also
 // endtask : axi4_write_data_phase
  //-------------------------------------------------------
  // Task: axi_write_data_phase
  // Samples the write data based on different burst types
  //-------------------------------------------------------

  task axi4_write_data_phase(axi4_write_transfer_char_s data_write_packet, axi4_transfer_cfg_s struct_cfg);

    //@(posedge aclk) begin
      `uvm_info(name,"INSIDE WRITE_DATA_PHASE",UVM_LOW)
      repeat(data_write_packet.no_of_wait_states)begin
        `uvm_info(name,$sformatf("DRIVING WAIT STATES :: %0d",data_write_packet.no_of_wait_states),UVM_HIGH);
        @(posedge aclk);
        wready<=0;
      end
      assign wready = wvalid;

   // data_write_packet.wready=wready;
     // wready <= 1;

      if(!aresetn)begin
      end
    //end

    //FIXED_Burst type
    
    @(posedge aclk)begin
      if(aresetn)begin
        for(int i = 0,k_t = 0;i<$size(mem_awid);i++)begin
          if(mem_wburst[i] == WRITE_FIXED)begin
            for(int j = 0;j<(mem_wlen[i]+1);j = j+1)begin
              for(int k = 0,k1 = 0;k1<(2**mem_wsize[i]);k1++)begin
                if(wstrb[k1])begin
                  data_write_packet.awaddr <= mem_waddr[i]+k-k_t; 
                  `uvm_info(name,$sformatf("w_addr = %0h",data_write_packet.awaddr),UVM_HIGH);
                  k++;
                  @(posedge aclk);
                end
                else begin
                  k++; 
                  k_t++;
                  @(posedge aclk);
                end
              end
            end
          end
         
          //INCR Burst type

          else if(mem_wburst[i] == WRITE_INCR)begin 
             for(int j = 0;j<(mem_wlen[i]+1);j = j+1)begin
               for(int k = 0,k1 = 0;k1<(2**mem_wsize[i]);k1++)begin
                 if(wstrb[k1])begin
                   data_write_packet.awaddr  <= mem_waddr[i]+(j*(2**mem_wsize[i]))+k-k_t;
                   `uvm_info(name,$sformatf("addr = %0h",data_write_packet.awaddr),UVM_HIGH);
                   k++;
                   @(posedge aclk);
                 end
                 else begin
                   k++; 
                   k_t++;
                   @(posedge aclk);
                 end
               end
             end
           end
           
         end
       end
      end
      
      for(int i1 = 0;i1<$size(mem_awid);i1++)begin
        if(mem_wburst[i1])begin
          `uvm_info(name,$sformatf("mem_burst[%0d] = %0h",i1,mem_wburst[i1]),UVM_HIGH);
          for(int n = 0;n<(2**mem_wsize[i1]);n++)begin
            if(wstrb[n])begin
              `uvm_info(name,$sformatf("mem_wstrb[%0d] = %0h",n,wstrb[n]),UVM_HIGH);
              data_write_packet.wdata <= wdata[n*8 +: 8];
              `uvm_info(name,$sformatf("wdata = %0h",data_write_packet.wdata),UVM_HIGH);
              @(posedge aclk);
            end
            else @(posedge aclk);
          end
        end
      end
  endtask

  task axi4_write_response_phase(axi4_write_transfer_char_s data_write_packet, axi4_transfer_cfg_s struct_cfg);
    @(posedge aclk)begin
      `uvm_info(name,"INSIDE WRITE RESPONSE PHASE",UVM_LOW)
      if(!aresetn)begin
        bresp <= 2'bz;
        bvalid = 0;
      end
      
      else begin
        bid_local = $urandom;  
        if(bid_local == mem_awid[i])begin   
          //bid  <= mem_awid[i];
          if(wready && wvalid)begin

          bid  <= mem_awid[i];
            bresp <= WRITE_OKAY;
            bvalid = 1;
            i++;
          end
          else begin
            bresp <= 2'bxx;
            bvalid = 0;
          end
        end
      end
    end
  endtask

  //-------------------------------------------------------
  // Task: axi4_write_response_phase
  // This task will drive the write response signals
  //-------------------------------------------------------
 // task axi4_write_response_phase (inout axi4_write_transfer_char_s data_write_packet, input axi4_transfer_cfg_s cfg_packet);
 //   `uvm_info(name,$sformatf("data_write_packet=\n%p",data_write_packet),UVM_HIGH)
 //   `uvm_info(name,$sformatf("cfg_packet=\n%p",cfg_packet),UVM_HIGH)
 //   `uvm_info(name,$sformatf("DRIVE TO WRITE RESPONSE CHANNEL"),UVM_HIGH)
 // bid=data_write_packet.bid;
 // bresp=data_write_packet.bresp;
 // bvalid=1;
 // while(!bready)begin 
 // @(posedge aclk);
 // bvalid=0;
 // end

 // endtask : axi4_write_response_phase
  //-------------------------------------------------------
  // Task: axi4_read_address_phase
  // This task will sample the read address signals
  //-------------------------------------------------------
  task axi4_read_address_phase (inout axi4_read_transfer_char_s data_read_packet, input axi4_transfer_cfg_s cfg_packet);
    `uvm_info(name,$sformatf("data_read_packet=\n%p",data_read_packet),UVM_HIGH);
    `uvm_info(name,$sformatf("cfg_packet=\n%p",cfg_packet),UVM_HIGH);
    `uvm_info(name,$sformatf("DRIVE TO READ ADDRESS CHANNEL"),UVM_HIGH);
    
     if(arvalid)begin
   // arready=1;
    data_read_packet.arid=arid;
    data_read_packet.araddr=araddr;
    data_read_packet.arlen = arlen;
    data_read_packet.arsize = arsize;
    data_read_packet.arburst = arburst;
    data_read_packet.arlock = arlock;
    data_read_packet.arcache = arcache;
    data_read_packet.arprot = arprot;
   end

    repeat(data_read_packet.no_of_wait_states)begin
      `uvm_info(name,$sformatf("DRIVING WAIT STATES :: %0d",data_read_packet.no_of_wait_states),UVM_HIGH);
      @(posedge aclk);
      arready<=0;
    end
    assign arready = arvalid;
   // data_read_packet.arready=arready;
    
    //awready <= 1;
 // if (arready==0) begin
  //   detect_read_address_wait_state(data_read_packet);
  //  end
  //  else begin
   //   arready=0;
   // end

  endtask : axi4_read_address_phase

  //-------------------------------------------------------
  // Task: axi4_read_data_channel_task
  // This task will drive the read data signals
  //-------------------------------------------------------
  task axi4_read_data_phase (inout axi4_read_transfer_char_s data_read_packet, input axi4_transfer_cfg_s cfg_packet);
    `uvm_info(name,$sformatf("data_read_packet=\n%p",data_read_packet),UVM_HIGH);
    `uvm_info(name,$sformatf("cfg_packet=\n%p",cfg_packet),UVM_HIGH);
    `uvm_info(name,$sformatf("DRIVE TO READ DATA CHANNEL"),UVM_HIGH);
    
  rid=data_read_packet.rid;
  rdata=data_read_packet.rdata;
  rresp=data_read_packet.rresp;
  rvalid=1;

   if(rready==0) begin
     detect_read_data_wait_state(data_read_packet);
   end;
 // while(!rready)begin 
  //@(posedge aclk);
  //rvalid=0;
  //end
  
  endtask : axi4_read_data_phase

endinterface : axi4_slave_driver_bfm

`endif
