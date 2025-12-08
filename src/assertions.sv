program apb_slv_assertion(PCLK, PRESETn, PADDR, PSEL, PENABLE, PWRITE, PWDATA, PSTRB, PRDATA, PREADY, PSLVERR);
	input PCLK;
	input PRESETn;

	input [`AW-1:0] PADDR;
	input PSEL;
	input PENABLE;
	input PWRITE;
	input [`DW-1:0] PWDATA;
	input [`DW/8-1:0] PSTRB;  
	input [`DW-1:0] PRDATA;
	input PREADY;
	input PSLVERR;     

	property p1;
		@(posedge PCLK) disable iff(!PRESETn) 
		(PSEL & PENABLE) |-> PREADY;
	endproperty

	property reset_check;
		@(posedge PCLK)
		(!PRESETn) |-> ((PREADY == 0) && (PRDATA == 0) && (PSLVERR == 0));
	endproperty

	property unknown_check;
		@(posedge PCLK) disable iff(!PRESETn)
		(!$isunknown(PREADY) && !$isunknown(PRDATA) && !$isunknown(PSLVERR) );
	endproperty

	property stability_check;
		@(posedge PCLK) disable iff(!PRESETn)
		(PSEL && PENABLE && !PREADY) |=> ($stable(PWRITE) && $stable(PADDR) && $stable(PWDATA) && $stable(PSTRB));
	endproperty

	property slverr_check; 
		@(posedge PCLK) disable iff(!PRESETn)
		PSLVERR |-> (PSEL && PENABLE && PREADY);
	endproperty

	property rdata_check;
		@(posedge PCLK) disable iff(!PRESETn)
		(PSEL && PENABLE && !PREADY) |-> (PRDATA == 0);
	endproperty

	a1: assert property(p1) $info("P1 PASS");
	else $error("P1 FAIL");

	a2_reset_check: assert property(p1) $info("reset_check PASS");
	else $error("reset_check FAIL");

	a3_unknown_check: assert property(unknown_check) $info("unknown_check PASS");
	else $error("unknown_check FAIL");

	a4_stability_check: assert property(stability_check) $info("stability_check PASS");
	else $error("stability_check FAIL");

	a5_slverr_check: assert property(slverr_check) $info("slverr_check PASS");
	else $error("slverr_check FAIL");

	a6_rdata_check: assert property(rdata_check) $info("rdata_check PASS");
	else $error("rdata_check FAIL");

endprogram

