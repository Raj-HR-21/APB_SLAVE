class base_test extends uvm_test;
	`uvm_component_utils(base_test)
	apb_slv_env env_h;
	apb_slv_sequence seq_h;

	function new(string name = "base_test", uvm_component parent = null);
		super.new(name, parent);
	endfunction
	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		env_h = apb_slv_env::type_id::create("env_h", this);

	endfunction: build_phase

	task run_phase(uvm_phase phase);
		phase.raise_objection(this);
		seq_h = apb_slv_sequence::type_id::create("seq_h");
		seq_h.start(env_h.a_agent_h.sqr_h);
		phase.drop_objection(this);
	endtask: run_phase
	function void end_of_elaboration_phase(uvm_phase phase);
		super.end_of_elaboration_phase(phase);
		uvm_top.print_topology
		();
	endfunction
endclass: base_test
/////////////////////////////////
//-------- only write -------- 
class write_test extends base_test;
	`uvm_component_utils(write_test)
	write_seq seq_h;

	function new(string name = "write_test", uvm_component parent = null);
		super.new(name, parent);
	endfunction

	task run_phase(uvm_phase phase);
		phase.raise_objection(this);
		seq_h = write_seq::type_id::create("seq_h");
		seq_h.start(env_h.a_agent_h.sqr_h);
		phase.drop_objection(this);
	endtask: run_phase

endclass: write_test
/////////////////////////////////
//-------- only read  -------- 
class read_test extends base_test;
	`uvm_component_utils(read_test)
	read_seq seq_h;

	function new(string name = "read_test", uvm_component parent = null);
		super.new(name, parent);
	endfunction

	task run_phase(uvm_phase phase);
		phase.raise_objection(this);
		seq_h = read_seq::type_id::create("seq_h");
		seq_h.start(env_h.a_agent_h.sqr_h);
		phase.drop_objection(this);
	endtask: run_phase

endclass: read_test 
/////////////////////////////////
//-------- random address write and read -------- 
class random_write_read_test extends base_test;
	`uvm_component_utils(random_write_read_test)
	random_write_read_seq seq_h;

	function new(string name = "random_write_read_test", uvm_component parent = null);
		super.new(name, parent);
	endfunction

	task run_phase(uvm_phase phase);
		phase.raise_objection(this);
		seq_h = random_write_read_seq::type_id::create("seq_h");
		seq_h.start(env_h.a_agent_h.sqr_h);
		phase.drop_objection(this);
	endtask: run_phase
endclass: random_write_read_test
/////////////////////////////////
//-------- write and read from same address -------- 
class write_then_read_test extends base_test;
	`uvm_component_utils(write_then_read_test)
	write_then_read_seq seq_h;

	function new(string name = "write_then_read_test", uvm_component parent = null);
		super.new(name, parent);
	endfunction

	task run_phase(uvm_phase phase);
		phase.raise_objection(this);
		seq_h = write_then_read_seq::type_id::create("seq_h");
		seq_h.start(env_h.a_agent_h.sqr_h);
		phase.drop_objection(this);
	endtask: run_phase
endclass: write_then_read_test
/////////////////////////////////
//-------- write and read from same address -------- 
class write_then_read_test2 extends base_test;
	`uvm_component_utils(write_then_read_test2)
	write_then_read_seq2 seq_h;

	function new(string name = "write_then_read_test2", uvm_component parent = null);
		super.new(name, parent);
	endfunction

	task run_phase(uvm_phase phase);
		phase.raise_objection(this);
		seq_h = write_then_read_seq2::type_id::create("seq_h");
		seq_h.start(env_h.a_agent_h.sqr_h);
		phase.drop_objection(this);
	endtask: run_phase
endclass: write_then_read_test2
/////////////////////////////////  
//-------- partial byte write with PSTRB and read from same address -------- 
class write_partial_bytes_test extends base_test;
	`uvm_component_utils(write_partial_bytes_test)
	write_partial_bytes_seq seq_h;

	function new(string name = "write_partial_bytes_test", uvm_component parent = null);
		super.new(name, parent);
	endfunction

	task run_phase(uvm_phase phase);
		phase.raise_objection(this);
		seq_h = write_partial_bytes_seq::type_id::create("seq_h");
		seq_h.start(env_h.a_agent_h.sqr_h);
		phase.drop_objection(this);
	endtask: run_phase
endclass: write_partial_bytes_test
/////////////////////////////////
//-------- Overwrite with different PSTRB patterns --------
class overwrite_with_strb_test extends base_test;
	`uvm_component_utils(overwrite_with_strb_test)
	overwrite_with_strb_seq seq_h;

	function new(string name = "overwrite_with_strb_test", uvm_component parent = null);
		super.new(name, parent);
	endfunction

	task run_phase(uvm_phase phase);
		phase.raise_objection(this);
		seq_h = overwrite_with_strb_seq::type_id::create("seq_h");
		seq_h.start(env_h.a_agent_h.sqr_h);
		phase.drop_objection(this);
	endtask: run_phase
endclass: overwrite_with_strb_test
/////////////////////////////////
//-------- No strobe for write --------
class no_pstrb_test extends base_test;
	`uvm_component_utils(no_pstrb_test)
	no_pstrb_seq seq_h;

	function new(string name = "no_pstrb_test", uvm_component parent = null);
		super.new(name, parent);
	endfunction

	task run_phase(uvm_phase phase);
		phase.raise_objection(this);
		seq_h = no_pstrb_seq::type_id::create("seq_h");
		seq_h.start(env_h.a_agent_h.sqr_h);
		phase.drop_objection(this);
	endtask: run_phase
endclass: no_pstrb_test
///////////////////////////////////
//-------- write to location byte wise --------
class byte_wise_write_test  extends base_test;
	`uvm_component_utils(byte_wise_write_test)
	byte_wise_write_seq seq_h;

	function new(string name = "byte_wise_write_test", uvm_component parent = null);
		super.new(name, parent);
	endfunction

	task run_phase(uvm_phase phase);
		phase.raise_objection(this);
		seq_h = byte_wise_write_seq::type_id::create("seq_h");
		seq_h.start(env_h.a_agent_h.sqr_h);
		phase.drop_objection(this);
	endtask: run_phase
endclass: byte_wise_write_test
////////////////////////////////////////////////////////////
//-------- invalid address --------
class invalid_addr_test extends base_test;
	`uvm_component_utils(invalid_addr_test)
	invalid_addr_seq seq_h;

	function new(string name = "invalid_addr_test", uvm_component parent = null);
		super.new(name, parent);
	endfunction

	task run_phase(uvm_phase phase);
		phase.raise_objection(this);
		seq_h = invalid_addr_seq::type_id::create("seq_h");
		seq_h.start(env_h.a_agent_h.sqr_h);
		phase.drop_objection(this);
	endtask: run_phase
endclass: invalid_addr_test 
//////////////////////////////////////////////////////////// 
class regression_test extends base_test;
	`uvm_component_utils(regression_test)
	regression_seq seq_h;

	function new(string name = "regression_test", uvm_component parent = null);
		super.new(name, parent);
	endfunction

	task run_phase(uvm_phase phase);
		phase.raise_objection(this);
		seq_h = regression_seq::type_id::create("seq_h");
		seq_h.start(env_h.a_agent_h.sqr_h);
		phase.drop_objection(this);
	endtask: run_phase
endclass: regression_test 

