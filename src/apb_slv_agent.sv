/////////////////////////////////////////////
//// Active Agent 
//////////////////////////////////////////////
class apb_slv_active_agent extends uvm_agent;
	`uvm_component_utils(apb_slv_active_agent)
	apb_slv_driver drv_h;
	apb_slv_active_monitor a_mon_h;
	apb_slv_sequencer sqr_h;

	function new(string name = "apb_slv_active_agent", uvm_component parent = null);
		super.new(name, parent);
	endfunction: new

	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		//if(!uvm_config_db#(uvm_active_passive_enum)::get(this, "", "is_active", is_active))
		//	`uvm_error("ACTIVE AGENT", "is_active undefines")

		if(get_is_active == UVM_ACTIVE) begin
			drv_h = apb_slv_driver::type_id::create("drv_h", this);
			sqr_h = apb_slv_sequencer::type_id::create("sqr_h", this);
		end
		a_mon_h = apb_slv_active_monitor::type_id::create("a_mon_h", this);
	endfunction: build_phase

	function void connect_phase(uvm_phase phase);
		super.connect_phase(phase);
		if(get_is_active() == UVM_ACTIVE)
			drv_h.seq_item_port.connect(sqr_h.seq_item_export);
	endfunction: connect_phase

endclass: apb_slv_active_agent

/////////////////////////////////////////////
//// Active Agent
//////////////////////////////////////////////


class apb_slv_passive_agent extends uvm_agent;
	`uvm_component_utils(apb_slv_passive_agent)
	apb_slv_passive_monitor p_mon_h;

	function new(string name = "apb_slv_passive_agent", uvm_component parent = null);
		super.new(name, parent);
	endfunction: new

	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		//if(!uvm_config_db#(uvm_active_passive_enum)::get(this, "", "is_active", is_active))
		//	`uvm_error("PASSIVE AGENT", "is_active undefines")
		p_mon_h = apb_slv_passive_monitor::type_id::create("p_mon_h", this);
	endfunction: build_phase

endclass: apb_slv_passive_agent

