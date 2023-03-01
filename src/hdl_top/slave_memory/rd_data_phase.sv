module rd_data_phase#(
parameter           AXI_DW         =  256          ,
parameter           AXI_AW         =  32           ,
parameter           AXI_IW         =   4           ,
parameter           AXI_SW         = AXI_DW >> 3   , 
parameter	    AXI_SI	   = 5
)
(
   input                          axi_clk_i      ,
   input                          axi_rstn_i     ,
   output reg      [ AXI_IW-1: 0] axi_rid_o      ,
   output reg      [ AXI_DW-1: 0] axi_rdata_o    ,
   output reg      [ AXI_SW-1: 0] axi_rstrb_o    ,
   output reg      [      2-1: 0] axi_rresp_o    ,
   output reg                     axi_rlast_o    ,
   output reg      [      4-1: 0] axi_ruser_o    ,
   output reg                     axi_rvalid_o   ,
   input		     	                axi_rready_i  
);

int size;
int i = 0,j=0,k_t=0,lower_wrap_addr,upper_wrap_addr,pos;

reg [AXI_DW-1:0] mem_rdata[256];

assign mem_top.sys_ren_o = ~mem_top.sys_wen_o;

always@(posedge axi_clk_i) begin
  if(axi_rstn_i) begin
    if(mem_top.sys_ren_o) begin
      if(mem_top.mem_rburst[i] == 2'b00) begin      
        axi_rid_o = mem_top.mem_rid[i];
        for(int len=0;len<mem_top.mem_rlen[i]+1;len++) begin
          mem_rdata[len] = 0;
          for(int g=0,int size=0;size<2**mem_top.mem_rsize[i];size++) begin
            mem_top.sys_addr_o  =  mem_top.mem_raddr[i] + g;
            $display("@%0t:adr:%0h,ac:%0h",$time(),mem_top.mem_raddr[i], mem_top.sys_addr_o);
            @(posedge mem_top.sys_clk_i);
            mem_rdata[len][pos*8+:8] = mem_top.sys_rdata_i; 
            //axi_rdata_o[size*8+:8] = mem_top.sys_rdata_i; 
            $display("rdd=%0d sys=%0d",axi_rdata_o[size*8+:8],mem_top.sys_rdata_i);
            axi_rresp_o = 2'b00;
            g++;
            pos++;
            if(pos==AXI_SW) pos = 0;
          end
          @(posedge axi_clk_i);
          axi_rdata_o = mem_rdata[len];
          axi_rvalid_o = 1'b1;
          wait(axi_rready_i==1);
        end
        axi_rlast_o = 1'b1;
        i++;
        @(posedge axi_clk_i);
        axi_rlast_o = 1'b0;
        axi_rvalid_o = 1'b0;
      end
    end
  end
end

always@(posedge axi_clk_i) begin
  if(axi_rstn_i) begin
    if(mem_top.sys_ren_o) begin
      if(mem_top.mem_rburst[i] == 2'b01) begin      
        axi_rid_o = mem_top.mem_rid[i];
        for(int g=0,int len=0;len<mem_top.mem_rlen[i]+1;len++) begin
          mem_rdata[len] = 0;
          for(int size=0;size<2**mem_top.mem_rsize[i];size++) begin
            mem_top.sys_addr_o  =  mem_top.mem_raddr[i] + g;
            $display("@%0t:adr:%0h,ac:%0h",$time(),mem_top.mem_raddr[i], mem_top.sys_addr_o);
            @(posedge mem_top.sys_clk_i);
            mem_rdata[len][pos*8+:8] = mem_top.sys_rdata_i; 
            //axi_rdata_o[size*8+:8] = mem_top.sys_rdata_i; 
            axi_rresp_o = 2'b00;
            g++;
            pos++;
            if(pos==AXI_SW) pos = 0;
          end
          @(posedge axi_clk_i);
          axi_rdata_o = mem_rdata[len];
          axi_rvalid_o = 1'b1;
          wait(axi_rready_i==1);
        end
        axi_rlast_o = 1'b1;
        i++;
        @(posedge axi_clk_i);
        axi_rlast_o = 1'b0;
        axi_rvalid_o = 1'b0;
      end
    end
  end
end


always@(posedge axi_clk_i) begin
  if(axi_rstn_i) begin
    if(mem_top.sys_ren_o) begin
      if(mem_top.mem_rburst[i] == 2'b10) begin      
        axi_rid_o = mem_top.mem_rid[i];
        lower_wrap_addr = mem_top.mem_raddr[i] - int'(mem_top.mem_raddr[i]%((mem_top.mem_rlen[i]+1)*(2**mem_top.mem_rsize[i])));
        upper_wrap_addr = lower_wrap_addr + ((mem_top.mem_rlen[i]+1)*(2**mem_top.mem_rsize[i])); 
        k_t =  mem_top.mem_raddr[i];
        for(int g=0,int len=0;len<mem_top.mem_rlen[i]+1;len++) begin
          mem_rdata[len] = 0;
          for(int size=0;size<2**mem_top.mem_rsize[i];size++) begin
            if(k_t<upper_wrap_addr) begin 
              mem_top.sys_addr_o  =  mem_top.mem_raddr[i] + g;
              g++;
              k_t++;
              if(k_t == upper_wrap_addr) g=0;              
            end
            else begin 
              mem_top.sys_addr_o  =  lower_wrap_addr + g;
              g++;
            end
            $display("@%0t:adr:%0h,ac:%0h",$time(),mem_top.mem_raddr[i], mem_top.sys_addr_o);
            @(posedge mem_top.sys_clk_i);
            $display("ll=%0h %0d",mem_rdata[len],len);
            mem_rdata[len][pos*8+:8] = mem_top.sys_rdata_i; 
            $display("rdd=%0h , %0d, po:%0d",mem_rdata[len][pos*8+:8],mem_top.sys_rdata_i,pos);
            axi_rresp_o = 2'b00;
            pos++;
            if(pos==AXI_SW) pos = 0;
          end
          @(posedge axi_clk_i);
          axi_rdata_o = mem_rdata[len];
          $display("ven:%0h,%0h %0d",axi_rdata_o,mem_rdata[len],len);
          axi_rvalid_o = 1'b1;
          wait(axi_rready_i==1);
           $display("ckk:%0d, %0d", axi_rdata_o,mem_rdata[len]);
        end
        axi_rlast_o = 1'b1;
        i++;
        @(posedge axi_clk_i);
        axi_rlast_o = 1'b0;
        axi_rvalid_o = 1'b0;
      end
    end
  end
end

endmodule




