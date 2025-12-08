class apb_slv_env extends uvm_env;
	`uvm_component_utils(apb_slv_env)
	apb_slv_active_agent a_agent_h;
	apb_slv_passive_agent p_agent_h;
	apb_slv_scoreboard scb_h;
	apb_slv_func_cov cov_h;

	function new(string name = "apb_slv_env", uvm_component parent = null);
		super.new(name, parent);
	endfunction: new
	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		a_agent_h = apb_slv_active_agent::type_id::create("a_agent_h", this);
		p_agent_h = apb_slv_passive_agent::type_id::create("p_agent_h", this);
		scb_h = apb_slv_scoreboard::type_id::create("scb_h", this);
		cov_h = apb_slv_func_cov::type_id::create("cov_h", this);

	endfunction: build_phase

	function void connect_phase(uvm_phase phase);
		super.connect_phase(phase);
		a_agent_h.a_mon_h.a_mon_port.connect(scb_h.act_mon_imp);
		p_agent_h.p_mon_h.p_mon_port.connect(scb_h.pas_mon_imp);
		
		a_agent_h.a_mon_h.a_mon_port.connect(cov_h.act_mon_imp);
		p_agent_h.p_mon_h.p_mon_port.connect(cov_h.pas_mon_imp);

	endfunction: connect_phase

endclass: apb_slv_env

