`ifndef AXI4_SLAVE_DRIVER_BFMNCLUDED_
`define AXI4_SLAVE_DRIVER_BFMNCLUDED_

//--------------------------------------------------------------------------------------------
//Interface : axi4_slave_driver_bfm
//Used as the HDL driver for axi4
//It connects with the HVL driver_proxy for driving the stimulus
//--------------------------------------------------------------------------------------------
import axi4_globals_pkg::*;
interface axi4_slave_driver_bfm(input                        aclk    , 
                                input                        aresetn ,
                                //Write_address_channel
                                input    [3:0]               awid    ,
                                input    [ADDRESS_WIDTH-1:0] awaddr  ,
                                input    [3: 0]              awlen   ,
                                input    [2: 0]              awsize  ,
                                input    [1: 0]              awburst ,
                                input    [1: 0]              awlock  ,
                                input    [3: 0]              awcache ,
                                input    [2: 0]              awprot  ,
                                input                        awvalid ,
                                output reg	                 awready ,

                                //Write_data_channel
                                input    [DATA_WIDTH-1: 0]     wdata  ,
                                input    [(DATA_WIDTH/8)-1: 0] wstrb  ,
                                input                          wlast  ,
                                input    [3: 0]                wuser  ,
                                input                          wvalid ,
                                output reg	                   wready ,

                                //Write Response Channel
                                output reg[3:0]                bid    ,
                                output reg[1:0]                bresp  ,
                                output reg[3:0]                buser  ,
                                output reg                     bvalid ,
                                input		                       bready ,

                                //Read Address Channel
                                input    [3: 0]                arid    ,
                                input    [ADDRESS_WIDTH-1: 0]  araddr  ,
                                input    [7:0]                 arlen   ,
                                input    [2:0]                 arsize  ,
                                input    [1:0]                 arburst ,
                                input    [1:0]                 arlock  ,
                                input    [3:0]                 arcache ,
                                input    [2:0]                 arprot  ,
                                input    [3:0]                 arQOS   ,
                                input    [3:0]                 arregion,
                                input    [3:0]                 aruser  ,
                                input                          arvalid ,
                                output reg                     arready ,

                                //Read Data Channel
                                output reg[3:0]                rid     ,
                                output reg[DATA_WIDTH-1: 0]    rdata   ,
                                output reg[(DATA_WIDTH/8)-1: 0]rstrb   ,
                                output reg[1:0]                rresp   ,
                                output reg                     rlast   ,
                                output reg[3:0]                ruser   ,
                                output reg                     rvalid  ,
                                input		                       rready  
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
      `uvm_info(name,$sformatf("SYSTEM RESET DI-ACTIVATED"),UVM_NONE)
    end
  endtask 
  
  //-------------------------------------------------------
  // Task: axi_write_address_phase
  // Sampling the signals that are associated with write_address_channel
  //-------------------------------------------------------

  task axi4_write_address_phase(axi4_write_transfer_char_s struct_write_pkt);
    @(posedge aclk)begin
      `uvm_info(name,"INSIDE WRITE_ADDRESS_PHASE",UVM_LOW)
      if(!aresetn)begin
      end
      else begin
        if(awvalid)begin
          mem_awid 	[i]	  <= awid  	;	
          //struct_write_pkt.awid = awid   ;
			    mem_waddr	[i] 	<= awaddr	;
          //struct_write_pkt.awaddr = awaddr;
			    mem_wlen 	[i]	  <= awlen	;	
          //struct_write_pkt.awlen = awlen;
			    mem_wsize	[i] 	<= awsize	;	
          //struct_write_pkt.awsize = awsize;
			    mem_wburst[i] 	<= awburst;	
          //struct_write_pkt.awburst = awburst;
			    mem_wlock	[i] 	<= awlock	;	
          //struct_write_pkt.awlock = awlock;
			    mem_wcache[i] 	<= awcache;	
          //struct_write_pkt.awcache = awcache;
			    mem_wprot	[i] 	<= awprot	;	
          //struct_write_pkt.awprot = awprot;
			    i <= i+1;
          for(int k=0;k<$size(mem_awid);k++) begin
            struct_write_pkt.awid = mem_awid[k];
            struct_write_pkt.awaddr = mem_waddr[k];
            struct_write_pkt.awlen = mem_wlen[k];
            struct_write_pkt.awsize = mem_wsize[k];
            struct_write_pkt.awburst = mem_wburst[k];
            struct_write_pkt.awlock = mem_wlock[k];
            struct_write_pkt.awcache = mem_wcache[k];
            struct_write_pkt.awprot = mem_wprot[k];
            `uvm_info(name,$sformatf("struct_pkt_wr_addr_phase = \n %0p",struct_write_pkt),UVM_HIGH)
          end
        end
      end
    end
    repeat(struct_write_pkt.no_of_wait_states)begin
      `uvm_info(name,$sformatf("DRIVING WAIT STATES :: %0d",struct_write_pkt.no_of_wait_states),UVM_HIGH);
      @(posedge aclk);
      awready<=0;
    end
    assign awready = awvalid;
    //awready <= 1;
  endtask

  //-------------------------------------------------------
  // Task: axi_write_data_phase
  // Samples the write data based on different burst types
  //-------------------------------------------------------

  task axi4_write_data_phase(axi4_write_transfer_char_s struct_write_pkt, axi4_transfer_cfg_s struct_cfg);

    @(posedge aclk) begin
      `uvm_info(name,"INSIDE WRITE_DATA_PHASE",UVM_LOW)
      repeat(struct_write_pkt.no_of_wait_states)begin
        `uvm_info(name,$sformatf("DRIVING WAIT STATES :: %0d",struct_write_pkt.no_of_wait_states),UVM_HIGH);
        @(posedge aclk);
        wready<=0;
      end
      assign wready = wvalid;
     // wready <= 1;

      if(!aresetn)begin
      end
    end

    //FIXED_Burst type
    
    @(posedge aclk)begin
      if(aresetn)begin
        for(int i = 0,k_t = 0;i<$size(mem_awid);i++)begin
          if(mem_wburst[i] == WRITE_FIXED)begin
            for(int j = 0;j<(mem_wlen[i]+1);j = j+1)begin
              for(int k = 0,k1 = 0;k1<(2**mem_wsize[i]);k1++)begin
                if(wstrb[k1])begin
                  struct_write_pkt.awaddr <= mem_waddr[i]+k-k_t; 
                  `uvm_info(name,$sformatf("w_addr = %0h",struct_write_pkt.awaddr),UVM_HIGH);
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
                   struct_write_pkt.awaddr  <= mem_waddr[i]+(j*(2**mem_wsize[i]))+k-k_t;
                   `uvm_info(name,$sformatf("addr = %0h",struct_write_pkt.awaddr),UVM_HIGH);
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
              struct_write_pkt.wdata <= wdata[n*8 +: 8];
              `uvm_info(name,$sformatf("wdata = %0h",struct_write_pkt.wdata),UVM_HIGH);
              @(posedge aclk);
            end
            else @(posedge aclk);
          end
        end
      end
  endtask

  task axi4_write_response_phase(axi4_write_transfer_char_s struct_write_pkt, axi4_transfer_cfg_s struct_cfg);
    @(posedge aclk)begin
      `uvm_info(name,"INSIDE WRITE RESPONSE PHASE",UVM_LOW)
      if(!aresetn)begin
        bresp <= 2'bz;
        bvalid = 0;
      end
      
      else begin
        bid_local = $urandom;  
        if(bid_local == mem_awid[i])begin   
          bid  <= mem_awid[i];
          if(wready && wvalid)begin
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
  // Task: axi4_read_address_channel_task
  // This task will drive the read address signals
  //-------------------------------------------------------
  task axi4_read_address_channel_task (inout axi4_read_transfer_char_s data_read_packet, input axi4_transfer_cfg_s cfg_packet);
    `uvm_info(name,$sformatf("data_read_packet=\n%p",data_read_packet),UVM_HIGH);
    `uvm_info(name,$sformatf("cfg_packet=\n%p",cfg_packet),UVM_HIGH);
    `uvm_info(name,$sformatf("DRIVE TO READ ADDRESS CHANNEL"),UVM_HIGH);
  endtask : axi4_read_address_channel_task

  //-------------------------------------------------------
  // Task: axi4_read_data_channel_task
  // This task will drive the read data signals
  //-------------------------------------------------------
  task axi4_read_data_channel_task (inout axi4_read_transfer_char_s data_read_packet, input axi4_transfer_cfg_s cfg_packet);
    `uvm_info(name,$sformatf("data_read_packet=\n%p",data_read_packet),UVM_HIGH);
    `uvm_info(name,$sformatf("cfg_packet=\n%p",cfg_packet),UVM_HIGH);
    `uvm_info(name,$sformatf("DRIVE TO READ DATA CHANNEL"),UVM_HIGH);
  endtask : axi4_read_data_channel_task

endinterface : axi4_slave_driver_bfm

`endif
