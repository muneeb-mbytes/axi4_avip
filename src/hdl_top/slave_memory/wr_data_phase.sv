
import axi4_globals_pkg::*;

module wr_data_phase#(
parameter           AXI_DW         =  256          ,
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
   input                     axi_wready_o  
);

reg [DATA_WIDTH-1:0]   mem_wdata  [int][256]; 
reg [STROBE_WIDTH-1:0] mem_wstrb  [int][256]; 


reg [7:0] temp = 0;
int l,k_t,i,k=0;

assign mem_top.sys_wen_o = (axi_wvalid_i || axi_wready_o) ;

always @(posedge axi_clk_i) begin
  if(axi_wvalid_i && axi_wready_o) begin
    mem_wdata[mem_top.mem_waddr[mem_top.wlast_cnt]][temp] = axi_wdata_i; 
    mem_wstrb[mem_top.mem_waddr[mem_top.wlast_cnt]][temp] = axi_wstrb_i; 
    temp = temp+1;
    if(axi_wlast_i) begin 
      mem_top.wlast_cnt++;
      temp = 0;
    end
  end
end



always@(posedge axi_clk_i)begin
	if(!axi_rstn_i)begin
	end
end

always@(posedge mem_top.sys_clk_i)begin
  if(axi_rstn_i) begin
    if(mem_top.sys_wen_o) begin
      if(mem_wdata.size()>0) begin
        for(int dupc=0;dupc<mem_wdata.size();dupc++) begin
           if(mem_top.mem_wburst[k] == 2'b00) begin
             for(i = 0;i<(mem_top.mem_wlen[k]+1);i++) begin
               for(int g=0,int l = 0;l<STROBE_WIDTH;l++) begin
                 if(mem_wstrb[mem_top.mem_waddr[k]][i][l]) begin
                   mem_top.sys_addr_o  <= mem_top.mem_waddr[k] + g;
                   mem_top.sys_wdata_o <= mem_wdata[mem_top.mem_waddr[k]][i][l*8 +: 8];
                  g++;
                 end
                 else begin
                 end
                 @(posedge mem_top.sys_clk_i);
               end 
             end
             mem_wdata.delete(mem_top.mem_waddr[k]);
             mem_wstrb.delete(mem_top.mem_waddr[k]);
             k++;
           end
        end
      end
    end
  end
end

always@(posedge mem_top.sys_clk_i)begin
  if(axi_rstn_i) begin
    if(mem_top.sys_wen_o) begin
      if(mem_wdata.size()>0) begin
        for(int g = 0,int dupc=0;dupc<mem_wdata.size();dupc++) begin
           if(mem_top.mem_wburst[k] == 2'b01) begin
             for(i = 0;i<(mem_top.mem_wlen[k]+1);i++) begin
               for(int l = 0;l<STROBE_WIDTH;l++) begin
                 if(mem_wstrb[mem_top.mem_waddr[k]][i][l]) begin
                   mem_top.sys_addr_o  <= mem_top.mem_waddr[k] + g;
                   mem_top.sys_wdata_o <= mem_wdata[mem_top.mem_waddr[k]][i][l*8 +: 8];
                  g++;
                 end
                 else begin
                 end
                 @(posedge mem_top.sys_clk_i);
               end 
             end
             mem_wdata.delete(mem_top.mem_waddr[k]);
             mem_wstrb.delete(mem_top.mem_waddr[k]);
             k++;
           end
        end
      end
    end
  end
end


always@(posedge mem_top.sys_clk_i)begin
  if(axi_rstn_i) begin
    if(mem_top.sys_wen_o) begin
      if(mem_wdata.size()>0) begin
        for(int dupc = 0,int g = 0,int lower_addr=0,int end_addr=0;dupc<mem_wdata.size();dupc++) begin
           if(mem_top.mem_wburst[k] == 2'b10) begin
             lower_addr = mem_top.mem_waddr[k] - int'(mem_top.mem_waddr[k]%((mem_top.mem_wlen[k]+1)*(2**mem_top.mem_wsize[k])));
             end_addr = lower_addr + ((mem_top.mem_wlen[k]+1)*(2**mem_top.mem_wsize[k]));
             k_t = mem_top.mem_waddr[k];
             for(i = 0;i<(mem_top.mem_wlen[k]+1);i++) begin
               for(int l = 0;l<STROBE_WIDTH;l++) begin
                 if(k_t < end_addr)  begin
                   if(mem_wstrb[mem_top.mem_waddr[k]][i][l]) begin
                     mem_top.sys_addr_o  = mem_top.mem_waddr[k] + g;
                     mem_top.sys_wdata_o = mem_wdata[mem_top.mem_waddr[k]][i][l*8 +: 8];
                    g++;
                    k_t++;
                   end
                   if(k_t == end_addr) g=0;
                 end
                 else begin 
                   if(mem_wstrb[mem_top.mem_waddr[k]][i][l]) begin
                     mem_top.sys_addr_o  = lower_addr + g;
                     mem_top.sys_wdata_o = mem_wdata[mem_top.mem_waddr[k]][i][l*8 +: 8];
                     g++;
                   end
                 end
                 @(posedge mem_top.sys_clk_i);
               end 
             end
             mem_wdata.delete(mem_top.mem_waddr[k]);
             mem_wstrb.delete(mem_top.mem_waddr[k]);
             k++;
           end
        end
      end
    end
  end
end

endmodule


