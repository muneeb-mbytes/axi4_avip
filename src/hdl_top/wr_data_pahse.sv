import axi4_globals_pkg::*;

module wr_data_phase#(
parameter           AXI_DW         = DATA_WIDTH    ,
parameter           AXI_AW         =  32           ,
parameter           AXI_IW         =   4           ,
parameter           AXI_SW         = AXI_DW >> 3   ,
parameter	          AXI_SI	       = 5
)
(
   input                     axi_clk_i      ,
   input                     axi_rstn_i     ,
   input      [ AXI_IW-1: 0] axi_wid_i      ,
   input      [ AXI_DW-1: 0] axi_wdata_i    ,
   input      [ AXI_SW-1: 0] axi_wstrb_i    ,
   input                     axi_wlast_i    ,
   input      [      4-1: 0] axi_wuser_i    ,
   input                     axi_wvalid_i   ,
   output reg		     axi_wready_o  
);

integer wrap = 0,start_bound = 0,end_bound = 0,l_t1 = 0,l_t2 = 0;
reg [3:0]a1 = 0;

assign axi_wready_o = axi_wvalid_i;   
assign axi_top_slave.sys_wen_o = axi_wvalid_i&&axi_wready_o&& !axi_top_slave.sys_ren_o;

always@(posedge axi_clk_i)begin
	if(!axi_rstn_i)begin
	end
end
always@(posedge axi_top_slave.sys_clk_i)begin
	if(axi_rstn_i&&axi_top_slave.sys_wen_o)begin
	 for(int i = 0,k_t = 0;i<$size(axi_top_slave.mem_wid);i++)begin
	  if(axi_top_slave.mem_wid[i] == axi_wid_i)begin  //
	   if(axi_top_slave.mem_wburst[i] == 2'b00)begin
	    for(int j = 0;j<(axi_top_slave.mem_wlen[i]+1);j = j+1)begin
	     if(axi_top_slave.sys_wen_o)begin
	      for(int k = 0,k1 = 0;k1<(2**axi_top_slave.mem_wsize[i]);k1++)begin
	       if(axi_wstrb_i[k1])begin
	    //	axi_top_slave.sys_addr_o  <= axi_top_slave.mem_waddr[i]+(j*(2**axi_top_slave.mem_wsize[i]))+k-k_t;
                axi_top_slave.sys_addr_o  <= axi_top_slave.mem_waddr[i]+k-k_t; //k_t increaments nly if stb is 0
	    //   $strobe("w_addr = %0h",axi_top_slave.sys_addr_o);
		k++;
	        @(posedge axi_top_slave.sys_clk_i);
	       end
	       else begin
		k++; 
		k_t++;
	        @(posedge axi_top_slave.sys_clk_i);
	       end
	      end
             end
	     else begin
	      if(j>=1) j--; // when w_en is 0 the slave is not ready to store the data so the length for loop will not increment it remains in same value(0)
	     end
	     @(posedge axi_top_slave.sys_clk_i);
	    end
	   end
           else if(axi_top_slave.mem_wburst[i] == 2'b01)begin // id matching
	    for(int j = 0;j<(axi_top_slave.mem_wlen[i]+1);j = j+1)begin
	     if(axi_top_slave.sys_wen_o)begin
	      for(int k = 0,k1 = 0;k1<(2**axi_top_slave.mem_wsize[i]);k1++)begin
	       if(axi_wstrb_i[k1])begin
		axi_top_slave.sys_addr_o  <= axi_top_slave.mem_waddr[i]+(j*(2**axi_top_slave.mem_wsize[i]))+k-k_t;
	//	$strobe("addr = %0h",axi_top_slave.sys_addr_o);
		k++;
	        @(posedge axi_top_slave.sys_clk_i);
	       end
	       else begin
		k++; 
		k_t++;
	        @(posedge axi_top_slave.sys_clk_i);
	       end
	      end
             end
	     else begin
	      if(j>=1) j--;
	     end
	     @(posedge axi_top_slave.sys_clk_i);
	    end
	   end
	   else if(axi_top_slave.mem_wburst[i] == 2'b10)begin
	    wrap = axi_top_slave.mem_waddr[i]/((2**axi_top_slave.mem_wsize[i])*(axi_top_slave.mem_wlen[i]+1));
	    start_bound = wrap*((2**axi_top_slave.mem_wsize[i])*(axi_top_slave.mem_wlen[i]+1));
	    end_bound = start_bound+((2**axi_top_slave.mem_wsize[i])*(axi_top_slave.mem_wlen[i]+1));
	    l_t1 = end_bound;
	    l_t2 = axi_top_slave.mem_waddr[i];
	    for(int w1 = l_t2,reg[2:0]w2 = 0,int w3 = 0;w1<l_t1;w2++,w1++)begin
	     if(axi_top_slave.sys_wen_o)begin
	      if(axi_wstrb_i[w2])begin
	       axi_top_slave.sys_addr_o <= w1;
	       if(w1 == axi_top_slave.mem_waddr[i]-1) break;
	      end
	      else w1--;
	      if(w1 == l_t1-1)begin
	       l_t1 = axi_top_slave.mem_waddr[i];
	       w1 = start_bound-1;
	      end
	      w3++;
	      if(w3 == ((2**axi_top_slave.mem_wsize[i])*(axi_top_slave.mem_wlen[i]+1))) break;
	      @(posedge axi_top_slave.sys_clk_i);
       	     end
	     else begin
	      w1--;
	      @(posedge axi_top_slave.sys_clk_i);
	     end
	    end
	   end
	   break;
	  end
	 end
        end
end

always@(posedge axi_top_slave.sys_clk_i)begin
	if(axi_top_slave.sys_wen_o)begin
	 for(int i1 = 0;i1<$size(axi_top_slave.mem_wid);i1++)begin
	  if(axi_top_slave.mem_wid[i1] == axi_wid_i)begin
        //       $display("mem_wid[%0d] = %0h axi_wid_i = %0h",i1,axi_top_slave.mem_wid[i1],axi_wid_i);
	   if(axi_top_slave.mem_wburst[i1] == 2'b00)begin
        //       $display("mem_burst[%0d] = %0h",i1,axi_top_slave.mem_wburst[i1]);
	    for(int n = 0;n<(2**axi_top_slave.mem_wsize[i1]);n++)begin
	     if(axi_wstrb_i[n])begin
        //        $display("mem_wstrb[%0d] = %0h",n,axi_wstrb_i[n]);
	           axi_top_slave.sys_wdata_o <= axi_wdata_i[n*8 +: 8];
         //        axi_wuser_i  <= 4'h0;
	 //       $strobe("wdata = %0h",axi_top_slave.sys_wdata_o);
	      @(posedge axi_top_slave.sys_clk_i);
	     end
	     else @(posedge axi_top_slave.sys_clk_i);
	    end
	   end
	  end
	 end
	end
end

always@(posedge axi_top_slave.sys_clk_i)begin
	if(axi_top_slave.sys_wen_o)begin
	 for(int i1 = 0;i1<$size(axi_top_slave.mem_wid);i1++)begin
	  if(axi_top_slave.mem_wid[i1] == axi_wid_i)begin
       //       $display("mem_wid[%0d] = %0h axi_wid_i = %0h",i1,axi_top_slave.mem_wid[i1],axi_wid_i);
	   if(axi_top_slave.mem_wburst[i1])begin
       //       $display("mem_burst[%0d] = %0h",i1,axi_top_slave.mem_wburst[i1]);
	    for(int n = 0;n<(2**axi_top_slave.mem_wsize[i1]);n++)begin
	     if(axi_wstrb_i[n])begin
           //     $display("mem_wstrb[%0d] = %0h",n,axi_wstrb_i[n]);
	         axi_top_slave.sys_wdata_o <= axi_wdata_i[n*8 +: 8];
           //   axi_wuser_i  <= 4'h0;
	   //   $strobe("wdata = %0h",axi_top_slave.sys_wdata_o);
	      @(posedge axi_top_slave.sys_clk_i);
	     end
	     else @(posedge axi_top_slave.sys_clk_i);
	    end
	   end
	  end
	 end
	end
end

endmodule


