`include "uvm_macros.svh"
`include "defines.sv"
`include "assertions.sv"
`include "interface.sv"
`include "apb_slave.v"

module top;

	import uvm_pkg::*;
	import apb_slv_pkg::*;
	bit PCLK;
	bit PRESETn;
	apb_slv_intf intf(PCLK, PRESETn);

	//dut instance
	apb_slave #(.ADDR_WIDTH(`AW), .DATA_WIDTH(`DW), .MEM_DEPTH(`MD))
	dut(	.PCLK(PCLK), .PRESETn(PRESETn),
		.PSEL(intf.PSEL), .PENABLE(intf.PENABLE), .PADDR(intf.PADDR), .PWDATA(intf.PWDATA), .PWRITE(intf.PWRITE), .PSTRB(intf.PSTRB),
		.PREADY(intf.PREADY), .PRDATA(intf.PRDATA), .PSLVERR(intf.PSLVERR)
	);
	bind intf apb_slv_assertion ASSERT(.*);
	always #5 PCLK = ~PCLK;
	initial begin
		PRESETn = 0;
		#10;
		PRESETn = 1;
		#20000;
		PRESETn = 0;
		#95;
		PRESETn = 1;
		#10;

	end

	initial begin
		uvm_config_db#(virtual apb_slv_intf)::set(null, "*", "vif", intf);

	//	run_test("write_test");
	//	run_test("read_test");
	//	run_test("random_write_read_test");
	//	run_test("write_then_read_test");
	//	run_test("write_then_read_test2");
	//	run_test("back_to_back_test");
	//	run_test("write_partial_bytes_test");
	//	run_test("overwrite_with_strb_test");
	//	run_test("no_pstrb_test");
	//	run_test("byte_wise_write_test");
	//	run_test("invalid_addr_test");

		run_test("regression_test");

	end
endmodule

