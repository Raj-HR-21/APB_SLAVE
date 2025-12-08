/////////////////////////////////////////////
// Active Monitor //
////////////////////////////////////////////
class apb_slv_active_monitor extends uvm_monitor;
	`uvm_component_utils(apb_slv_active_monitor)
	virtual apb_slv_intf vif;
	uvm_analysis_port#(apb_slv_seq_item) a_mon_port;
	apb_slv_seq_item in_item;

	function new(string name = "apb_slv_active_monitor",  uvm_component parent = null);
		super.new(name, parent);
	endfunction: new
	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		a_mon_port = new("a_mon_port", this);
		if( !(uvm_config_db#(virtual apb_slv_intf)::get(this, "", "vif", vif) ))
			`uvm_error("ACTIVE MONITOR", "NO VIRTUAL INTERFACE IN ACTIVE MONITOR")
	endfunction: build_phase

	task run_phase(uvm_phase phase);
		repeat(2)@(vif.mon_cb);
		forever begin
			in_item = apb_slv_seq_item::type_id::create("in_item");
			//repeat(1)@(vif.mon_cb);
			wait(vif.mon_cb.PSEL && vif.mon_cb.PENABLE && vif.mon_cb.PREADY);
			in_item.PSEL 	= vif.PSEL;
			in_item.PENABLE = vif.PENABLE;
			in_item.PWRITE  = vif.PWRITE;
			in_item.PADDR   = vif.PADDR;
			in_item.PWDATA  = vif.PWDATA;
			in_item.PSTRB   = vif.PSTRB;

			`uvm_info("ACT-MON ", $sformatf("\nPENABLE = %0d | PSEL = %0d | PWRITE = %0d | PSTRB = %b | PWDATA = %h | PADDR = %0d\n", in_item.PENABLE, in_item.PSEL, in_item.PWRITE, in_item.PSTRB, in_item.PWDATA, in_item.PADDR), UVM_LOW)
			a_mon_port.write(in_item);
			repeat(1)@(vif.mon_cb);
		end
	endtask: run_phase

endclass: apb_slv_active_monitor

/////////////////////////////////////////////
// Passive Monitor //
////////////////////////////////////////////
class apb_slv_passive_monitor extends uvm_monitor;
	`uvm_component_utils(apb_slv_passive_monitor)
	virtual apb_slv_intf vif;
	uvm_analysis_port#(apb_slv_seq_item) p_mon_port;
	apb_slv_seq_item out_item;

	function new(string name = "apb_slv_passive_monitor",  uvm_component parent = null);
		super.new(name, parent);
	endfunction: new
	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		p_mon_port = new("p_mon_port", this);
		if( !(uvm_config_db#(virtual apb_slv_intf)::get(this, "", "vif", vif) ))
			`uvm_error("PASSIVE MONITOR", "NO VIRTUAL INTERFACE IN PASSIVE MONITOR")
	endfunction: build_phase

	task run_phase(uvm_phase phase);
		repeat(2)@(vif.mon_cb);
		forever begin
			out_item = apb_slv_seq_item::type_id::create("out_item");
			wait(vif.mon_cb.PSEL && vif.mon_cb.PENABLE && vif.mon_cb.PREADY );
			//repeat(1)@(vif.mon_cb);
			out_item.PSLVERR = vif.PSLVERR;
			out_item.PRDATA  = vif.PRDATA;
			out_item.PREADY  = vif.PREADY;
			`uvm_info("PAS-MON", $sformatf("\nPREADY = %0d | PRDATA = %h | PSLVERR = %0d\n", out_item.PREADY, out_item.PRDATA, out_item.PSLVERR), UVM_LOW)
			p_mon_port.write(out_item);
			repeat(1)@(vif.mon_cb);
		end
	endtask: run_phase


endclass: apb_slv_passive_monitor


