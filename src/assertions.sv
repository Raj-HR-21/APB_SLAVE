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

	property reset_check;
		@(posedge PCLK)
		(!PRESETn) |-> ((PREADY == 0)&&(PSLVERR == 0)&&(PRDATA == 0));
	endproperty
	a1_reset_check: assert property(reset_check) $info("reset_check PASS");
	else $error("reset_check FAIL PREADY=%0d",PREADY);

	//-----------------------------------------------------------
	property no_wait_state_check;
		@(posedge PCLK) disable iff(!PRESETn) 
		(PSEL & PENABLE) |-> PREADY;
	endproperty
	a2_no_wait_state_check: assert property(no_wait_state_check) $info("no_wait_state_check PASS");
	else $error("no_wait_state_check FAIL");
	//-----------------------------------------------------------
	property unknown_check;
		@(posedge PCLK) disable iff(!PRESETn)
		(!$isunknown(PREADY) && !$isunknown(PRDATA) && !$isunknown(PSLVERR) );
	endproperty
	a3_unknown_check: assert property(unknown_check) $info("unknown_check PASS");
	else $error("unknown_check FAIL");
	//-----------------------------------------------------------
	property stability_check;
		@(posedge PCLK) disable iff(!PRESETn)
		(PSEL && PENABLE && !PREADY) |=> ($stable(PWRITE) && $stable(PADDR) && $stable(PWDATA) && $stable(PSTRB));
	endproperty
	a4_stability_check: assert property(stability_check) $info("stability_check PASS");
	else $error("stability_check FAIL");
	//-----------------------------------------------------------
	property slverr_valid; 
		@(posedge PCLK) disable iff(!PRESETn)
		PSLVERR |-> (PSEL && PENABLE && PREADY);
	endproperty
	a5_slverr_valid: assert property(slverr_valid) $info("slverr_valid PASS");
	else $error("slverr_valid FAIL");
	//-----------------------------------------------------------
	property slverr_check; 
		@(posedge PCLK) disable iff(!PRESETn)
		(PSEL && PENABLE && PREADY && (PADDR >= `MD)) |-> PSLVERR;
	endproperty
	a6_slverr_check: assert property(slverr_valid) $info("slverr_check PASS");
	else $error("slverr_check FAIL");

endprogram
