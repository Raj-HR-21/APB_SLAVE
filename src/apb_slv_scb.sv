`uvm_analysis_imp_decl(_a_mon)
`uvm_analysis_imp_decl(_p_mon)

class apb_slv_scoreboard extends uvm_scoreboard;
	`uvm_component_utils(apb_slv_scoreboard)
	uvm_analysis_imp_a_mon#(apb_slv_seq_item, apb_slv_scoreboard) act_mon_imp;
	uvm_analysis_imp_p_mon#(apb_slv_seq_item, apb_slv_scoreboard) pas_mon_imp;
	
	apb_slv_seq_item q_act_mon[$];
	apb_slv_seq_item q_pas_mon[$];
	virtual apb_slv_intf vif;
	
	int total_write, total_read;
	int pready_pass, pready_fail;
	int prdata_pass, prdata_fail;
	int slv_err_pass, slv_err_fail;
	bit [`DW-1 :0]mem[0:`MD-1];
	
	function new(string name = "apb_slv_scoreboard", uvm_component parent = null);
		super.new(name, parent);
	endfunction: new
	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		act_mon_imp = new("act_mon_imp", this);
		pas_mon_imp = new("pas_mon_imp", this);
		if( !(uvm_config_db#(virtual apb_slv_intf)::get(this, "", "vif", vif) ))
			`uvm_error(" SCB ", "NO VIRTUAL INTERFACE IN SCB")
	endfunction: build_phase
	
	function void write_a_mon(apb_slv_seq_item inp);
		q_act_mon.push_back(inp);
		`uvm_info("SCB", $sformatf("Input item sent to queue"), UVM_LOW)
	endfunction: write_a_mon
	
	function void write_p_mon(apb_slv_seq_item out);
		q_pas_mon.push_back(out);
		`uvm_info("SCB", $sformatf("Output item sent to queue"), UVM_LOW)
	endfunction: write_p_mon

	task run_phase(uvm_phase phase);
		apb_slv_seq_item inp_item = apb_slv_seq_item::type_id::create("inp_item");
		apb_slv_seq_item out_item = apb_slv_seq_item::type_id::create("out_item"); //dut response
		apb_slv_seq_item expt = apb_slv_seq_item::type_id::create("expt");
		int bytes = `DW/8;
		forever begin
			//=====================================================================================
			//RESET
			if(!vif.PRESETn) begin
				foreach(mem[i]) mem[i] = 0;
				expt.PSLVERR = 0;
				expt.PRDATA = 0;
				q_act_mon.delete();
				q_pas_mon.delete();
				`uvm_info("SCB_RESET", $sformatf("RESET"), UVM_LOW)
			end

			wait(q_act_mon.size() > 0 && q_pas_mon.size() > 0);
			inp_item = q_act_mon.pop_front();
			out_item = q_pas_mon.pop_front();
			
			//=====================================================================================
			// WRITE
			if(inp_item.PSEL && inp_item.PENABLE && inp_item.PWRITE) begin : write_op
				total_write++;
				expt.PREADY = 1;

				if(inp_item.PADDR < `MD) begin
					expt.PSLVERR = 0;
					for(int i = 0; i < bytes; i++) begin
						if(inp_item.PSTRB[i])
							mem[inp_item.PADDR][i*8 +: 8] = inp_item.PWDATA[i*8 +: 8];
						expt.PRDATA = 'b0;
					end
				end
				else begin 
					expt.PSLVERR = 1;
				end
				//compare----------------------------------------------------------------------------
				if(expt.PREADY != out_item.PREADY) begin
					pready_fail++;
					`uvm_info("SCB", $sformatf("PREADY mismatch expt = %0d | actual = %0d\n", expt.PREADY, out_item.PREADY), UVM_LOW)
				end
				else begin
					pready_pass++;
					`uvm_info("SCB", $sformatf("PREADY match"), UVM_LOW)
				end
				if(expt.PSLVERR != out_item.PSLVERR) begin
					slv_err_fail++;
					`uvm_info("SCB", $sformatf("Slave error mismatch: expt = %0d | actual = %0d\n", expt.PSLVERR, out_item.PSLVERR), UVM_LOW)
				end
				else begin
					slv_err_pass++;
					`uvm_info("SCB", $sformatf("Slave error match"), UVM_LOW)
				end
			end : write_op
			//=====================================================================================
			//READ
			else if(inp_item.PSEL && inp_item.PENABLE && !inp_item.PWRITE) begin : read_op
				total_read++;

				if(inp_item.PADDR < `MD) begin
					expt.PRDATA = mem[inp_item.PADDR];
					expt.PSLVERR = 0;
				end
				else if(inp_item.PADDR >= `MD) begin
					//expt.PRDATA = {`DW{1'b1}};
					expt.PSLVERR = 1;
				end
				else begin
					expt.PRDATA = 'b0;
					expt.PSLVERR = 0;
				end
				`uvm_info("SCB_EXP_RD", $sformatf("\nPREADY = %0d | PSLVERR = %0d | PRDATA = %h\n", expt.PREADY, expt.PSLVERR, expt.PRDATA), UVM_LOW)
				//compare----------------------------------------------------------------------------
				if(expt.PREADY != out_item.PREADY) begin
					pready_fail++;
					`uvm_info("SCB", $sformatf("PREADY mismatch expt = %0d | actual = %0d\n", expt.PREADY, out_item.PREADY), UVM_LOW)
				end
				else begin
					pready_pass++;
					`uvm_info("SCB", $sformatf("PREADY match"), UVM_LOW)
				end

				if(expt.PSLVERR != out_item.PSLVERR) begin
					slv_err_fail++;
					`uvm_info("SCB", $sformatf("Slave error mismatch: expt = %0d | actual = %0d\n", expt.PSLVERR, out_item.PSLVERR), UVM_LOW)
				end
				else begin
					slv_err_pass++;
					`uvm_info("SCB", $sformatf("Slave error match"), UVM_LOW)
				end

				if((expt.PRDATA != out_item.PRDATA) && (!out_item.PSLVERR)) begin
					prdata_fail++;
					`uvm_info("SCB", $sformatf("RDATA mismatch : expt.PRDATA = %h | actual.PRDATA = %h\n", expt.PRDATA, out_item.PRDATA), UVM_LOW)
				end
				else begin
					prdata_pass++;
					`uvm_info("SCB", $sformatf("PRDATA match : expt.PRDATA = %h | actual.PRDATA = %h\n", expt.PRDATA, out_item.PRDATA), UVM_LOW)
				end
			end : read_op
		end
	endtask: run_phase
	
	function void report_phase(uvm_phase phase);
		super.report_phase(phase);
		$display("");
		`uvm_info("SCB", $sformatf("Total write = %0d | Total read = %0d", total_write, total_read), UVM_NONE)
		`uvm_info("SCB", $sformatf("PREADY pass = %0d | PREADY fail = %0d", pready_pass, pready_fail), UVM_NONE)
		`uvm_info("SCB", $sformatf("Read data pass = %0d | Read data fail = %0d", prdata_pass, prdata_fail), UVM_NONE)
		`uvm_info("SCB", $sformatf("Slave error pass = %0d | Slave error fail = %0d", slv_err_pass, slv_err_fail), UVM_NONE)

	endfunction: report_phase

endclass




