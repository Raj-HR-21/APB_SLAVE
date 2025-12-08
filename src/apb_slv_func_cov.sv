`uvm_analysis_imp_decl(_act_mon)
`uvm_analysis_imp_decl(_pas_mon)

class apb_slv_func_cov extends uvm_scoreboard;
	`uvm_component_utils(apb_slv_func_cov)
	uvm_analysis_imp_act_mon#(apb_slv_seq_item, apb_slv_func_cov) act_mon_imp;
	uvm_analysis_imp_pas_mon#(apb_slv_seq_item, apb_slv_func_cov) pas_mon_imp;
	
	apb_slv_seq_item act_mon_item, pas_mon_item;
	real inp_cov, out_cov;
	
	covergroup inp_cg;
		cp_sel	: coverpoint act_mon_item.PSEL { 
			bins psel_bin_0 = {0};
			bins psel_bin_1 = {1};
		}
		cp_en	: coverpoint act_mon_item.PENABLE { 
			bins pen_bin_0 = {0};
			bins pen_bin_1 = {1};
		}
		cp_wr_rd: coverpoint act_mon_item.PWRITE { 
			bins write_bin = {1};
			bins read_bin = {0}; 
		}
		cp_wdata: coverpoint act_mon_item.PWDATA { 
			bins wdata[5] = {[0: `DW'hFFFFFFFF]}; 	
		}
		cp_addr	: coverpoint act_mon_item.PADDR { 
			bins addr[5] = {[0: `AW'hFF]}; 
		}
		cp_strb	: coverpoint act_mon_item.PSTRB { 
			bins strb[] = {[0: 15]};
		}

		wr_x_en: cross cp_wr_rd, cp_en{
			bins cover_bin = (binsof(cp_wr_rd) && (binsof(cp_en) intersect {1}) );
			ignore_bins no_cov = (binsof(cp_wr_rd) && (binsof(cp_en) intersect {0}) );
		}
		wr_x_sel: cross cp_wr_rd, cp_sel{
			bins cover_bin = (binsof(cp_wr_rd) && (binsof(cp_sel) intersect {1}) );
			ignore_bins no_cov = (binsof(cp_wr_rd) && (binsof(cp_sel) intersect {0}) );
		}

	endgroup

	covergroup out_cg;
		cp_ready : coverpoint pas_mon_item.PREADY { 
			bins ready_0 = {0};
			bins ready_1 = {1}; 
		}
		cp_slverr: coverpoint pas_mon_item.PSLVERR{ 
			bins err = {1};
			bins no_err = {0}; 
		}
		cp_rdata : coverpoint pas_mon_item.PRDATA { 
			bins rdata_0 = {0};
			bins rdata[5] = {[1: `DW'hFFFFFFFF]};
		}

		rdy_x_err: cross cp_ready, cp_slverr{
			bins cov = ((binsof(cp_ready) intersect {1}) && binsof(cp_slverr) );
			ignore_bins no_cov = ((binsof(cp_ready) intersect {0}) && binsof(cp_slverr) );
		}

		
	endgroup

	function new(string name = "slv_func_cov", uvm_component parent = null);
		super.new(name, parent);
		inp_cg = new();
		out_cg = new();
	endfunction: new
	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		act_mon_imp = new("act_mon_imp", this);
		pas_mon_imp = new("pas_mon_imp", this);
	endfunction: build_phase
	
	function void write_act_mon(apb_slv_seq_item inp);
		act_mon_item = inp;
		inp_cg.sample();
	endfunction: write_act_mon
	
	function void write_pas_mon(apb_slv_seq_item out);
		pas_mon_item = out;
		out_cg.sample();
	endfunction: write_pas_mon

	function void extract_phase(uvm_phase phase);
		super.extract_phase(phase);
		inp_cov = inp_cg.get_coverage();
		out_cov = out_cg.get_coverage();
	endfunction: extract_phase

	function void report_phase(uvm_phase phase);
		super.extract_phase(phase);
		`uvm_info("Func_cvg", $sformatf("Input coverage = %.4f", inp_cov), UVM_LOW)
		`uvm_info("Func_cvg", $sformatf("Output coverage = %.4f", out_cov), UVM_LOW)
	endfunction: report_phase

endclass: apb_slv_func_cov


