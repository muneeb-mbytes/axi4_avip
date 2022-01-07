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
                                input    [15:0]              awid    ,
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
                                output reg[15:0]               bid    ,
                                output reg[1:0]                bresp  ,
                                output reg[3:0]                buser  ,
                                output reg                     bvalid ,
                                input		                       bready ,

                                //Read Address Channel
                                input    [15: 0]               arid    ,
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
                                output reg[15:0]               rid     ,
                                output reg[DATA_WIDTH-1: 0]    rdata   ,
                                output reg[(DATA_WIDTH/8)-1: 0]rstrb   ,
                                output reg[1:0]                rresp   ,
                                output reg                     rlast   ,
                                output reg[3:0]                ruser   ,
                                output reg                     rvalid  ,
                                input		                       rready  
                              ); 
                              
  // Internal signals
  //reg                           sys_clk_i      ;  
   reg      [ ADDRESS_WIDTH-1: 0] sys_addr_o     ;  
   reg      [ 8-1: 0]             sys_wdata_o    ;  
  //reg     [ AXI_SW-1: 0]        sys_sel_o      ;  
   reg                            sys_wen_o      ;  
   reg                            sys_ren_o      ;  
   reg      [ 8-1: 0]             sys_rdata_i    ; 

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
  
  reg[3:0] i = 0;
  reg [3:0] a1 = 0;
  integer wrap = 0,start_bound = 0,end_bound = 0,l_t1 = 0,l_t2 = 0;

  initial begin
    `uvm_info("axi4 slave driver bfm",$sformatf("AXI4 SLAVE DRIVER BFM"),UVM_LOW);
  end

  string name = "AXI4_SLAVE_DRIVER_BFM";

  // Creating Memories for each signal to store each transaction attributes

  reg [	15: 0]	            mem_awid	  [1024];
  reg [	ADDRESS_WIDTH-1: 0]	mem_waddr	  [1024];
  reg [	7:0]	              mem_wlen	  [256] ;
  reg [	2:0]	              mem_wsize	  [1024];
  reg [ 1	: 0]	            mem_wburst  [1024];
  reg [ 1	: 0]	            mem_wlock	  [1024];
  reg [ 3	: 0]	            mem_wcache  [1024];
  reg [ 2	: 0]	            mem_wprot	  [1024];
  reg [ 3	: 0]	            mem_wQOS  	[1024];
  reg [ 3	: 0]	            mem_wregion	[1024];
  reg [ 3	: 0]	            mem_wuser	  [1024];

  reg [	15: 0]	            mem_rid		  [1024];
  reg [	ADDRESS_WIDTH-1: 0]	mem_raddr	  [1024];
  reg [	7	: 0]	            mem_rlen	  [256];
  reg [	2	: 0]	            mem_rsize	  [1024];
  reg [ 1	: 0]	            mem_rburst  [1024];
  reg [ 1	: 0]	            mem_rlock	  [1024];
  reg [ 3	: 0]	            mem_rcache  [1024];
  reg [ 2	: 0]	            mem_rprot	  [1024];
  reg [ 3	: 0]	            mem_rQOS   	[1024];
  reg [ 3	: 0]	            mem_rregion [1024];
  reg [ 3	: 0]	            mem_ruser	  [1024];

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
        //  for(int k=0;k<$size(mem_awid);k++) begin
        //    struct_write_pkt.awid = mem_awid[k];
        //    struct_write_pkt.awaddr = mem_waddr[k];
        //    struct_write_pkt.awlen = mem_wlen[k];
        //    struct_write_pkt.awsize = mem_wsize[k];
        //    struct_write_pkt.awburst = mem_wburst[k];
        //    struct_write_pkt.awlock = mem_wlock[k];
        //    struct_write_pkt.awcache = mem_wcache[k];
        //    struct_write_pkt.awprot = mem_wprot[k];
        //    `uvm_info(name,$sformatf("struct_pkt_wr_addr_phase = \n %0p",struct_write_pkt),UVM_HIGH)
        //  end
        end
      end
    end
    repeat(struct_write_pkt.no_of_wait_states)begin
      `uvm_info(name,$sformatf("DRIVING WAIT STATES :: %0d",struct_write_pkt.no_of_wait_states),UVM_HIGH);
      @(posedge aclk);
      awready<=0;
    end
    assign awready = awvalid;
  endtask

  //-------------------------------------------------------
  // Task: axi_write_data_phase
  // Samples the write data based on different burst types
  //-------------------------------------------------------

  task axi_write_data_phase(axi4_write_transfer_char_s struct_write_pkt, axi4_transfer_cfg_s struct_cfg);
    @(posedge aclk) begin
      `uvm_info(name,"INSIDE WRITE_DATA_PHASE",UVM_LOW)
      assign wready = wvalid;
      assign sys_wen_o = wvalid && wready && !sys_ren_o;
      if(!aresetn)begin
      end
    end

    //FIXED_Burst type
    
    @(posedge aclk)begin
      if(aresetn&&sys_wen_o)begin
        for(int i = 0,k_t = 0;i<$size(mem_awid);i++)begin
          if(mem_wburst[i] == WRITE_FIXED)begin
            for(int j = 0;j<(mem_wlen[i]+1);j = j+1)begin
              if(sys_wen_o)begin
                for(int k = 0,k1 = 0;k1<(2**mem_wsize[i]);k1++)begin
                  if(wstrb[k1])begin
                    sys_addr_o  <= mem_waddr[i]+k-k_t; 
                    `uvm_info(name,$sformatf("w_addr = %0h",sys_addr_o),UVM_HIGH);
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
              else begin
                if(j>=1) j--;
              end
              @(posedge aclk);
            end
          end
         
          //INCR Burst type

          else if(mem_wburst[i] == WRITE_INCR)begin 
             for(int j = 0;j<(mem_wlen[i]+1);j = j+1)begin
               if(sys_wen_o)begin
                 for(int k = 0,k1 = 0;k1<(2**mem_wsize[i]);k1++)begin
                   if(wstrb[k1])begin
                     sys_addr_o  <= mem_waddr[i]+(j*(2**mem_wsize[i]))+k-k_t;
	                   `uvm_info(name,$sformatf("addr = %0h",sys_addr_o),UVM_HIGH);
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
              else begin
                 if(j>=1) j--;
               end
               @(posedge aclk);
             end
           end
           
           //WRAP Burst type

   //        else if(mem_wburst[i] == WRITE_WRAP)begin
   //         wrap = mem_waddr[i]/((2**mem_wsize[i])*(mem_wlen[i]+1));
	 //         start_bound = wrap*((2**mem_wsize[i])*(mem_wlen[i]+1));
   //         end_bound = start_bound+((2**mem_wsize[i])*(mem_wlen[i]+1));
   //         l_t1 = end_bound;
	 //         l_t2 = mem_waddr[i];
	 //         for(int w1 = l_t2,reg[2:0]w2 = 0,int w3 = 0;w1<l_t1;w2++,w1++)begin
   //           if(sys_wen_o)begin
   //             if(wstrb[w2])begin
   //               sys_addr_o <= w1;
   //               if(w1 == mem_waddr[i]-1) break;
   //             end
   //             else w1--;
   //             if(w1 == l_t1-1)begin
   //               l_t1 = mem_waddr[i];
   //               w1 = start_bound-1;
   //             end
   //             w3++;
   //             if(w3 == ((2**mem_wsize[i])*(mem_wlen[i]+1))) break;
   //             @(posedge aclk);
   //           end
   //           else begin
   //             w1--;
	 //             @(posedge aclk);
   //           end
   //         end
   //       end
   //       break;
        end
      end
    end
    
    // wdata for each burst type
    
 //   @(posedge aclk)begin
 //     if(sys_wen_o)begin
 //       for(int i1 = 0;i1<$size(mem_awid);i1++)begin
 //         if(mem_wburst[i1])begin
 //           $display("mem_burst[%0d] = %0h",i1,mem_wburst[i1]);
 //           for(int n = 0;n<(2**mem_wsize[i1]);n++)begin
 //             if(wstrb[n])begin
 //               $display("mem_wstrb[%0d] = %0h",n,wstrb[n]);
 //               sys_wdata_o <= wdata[n*8 +: 8];
 //               struct_write_pkt.wdata <= wdata[n*8 +: 8];
 //               //axi_wuser_i  <= 4'h0;
 //               $strobe("wdata = %0h",sys_wdata_o);
 //               @(posedge aclk);
 //             end
 //             else @(posedge aclk);
 //           end
 //         end
 //       end
 //     end
 //   end
  endtask


endinterface : axi4_slave_driver_bfm

`endif
