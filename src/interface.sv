interface apb_slv_intf(input bit PCLK, input bit PRESETn);

	logic PENABLE;
	logic PSEL;
	logic PWRITE;
	logic [`AW-1 :0]PADDR;
	logic [`DW-1 :0]PWDATA;
	logic [(`DW/8)-1 :0]PSTRB;

	logic PREADY;
	logic PSLVERR;
	logic [`DW-1 :0]PRDATA;

	clocking drv_cb @(posedge PCLK);
		default input #0 output #0;
		output PENABLE, PSEL, PWRITE, PWDATA, PADDR, PSTRB;
		input PREADY;
	endclocking
	clocking mon_cb @(posedge PCLK);
		default input #0 output #0;
		input PRESETn, PENABLE, PSEL, PWRITE, PWDATA, PADDR, PSTRB;
		input PSLVERR, PREADY, PRDATA;
	endclocking 
	
endinterface: apb_slv_intf

