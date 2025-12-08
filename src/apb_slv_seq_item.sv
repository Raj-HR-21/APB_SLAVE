class apb_slv_seq_item extends uvm_sequence_item;

	rand logic PENABLE;
	rand logic PSEL;
	rand logic PWRITE;
	rand logic [`DW-1 :0]PWDATA;
	rand logic [`AW-1 :0]PADDR;
	rand logic [(`DW/8)-1 :0]PSTRB;

	logic PREADY;
	logic PSLVERR;
	logic [`DW-1 :0]PRDATA;

	`uvm_object_utils_begin(apb_slv_seq_item)
	`uvm_field_int(PENABLE, UVM_ALL_ON)
	`uvm_field_int(PSEL, UVM_ALL_ON)
	`uvm_field_int(PWRITE, UVM_ALL_ON)
	`uvm_field_int(PWDATA, UVM_ALL_ON)
	`uvm_field_int(PADDR, UVM_ALL_ON)
	`uvm_field_int(PSTRB, UVM_ALL_ON)

	`uvm_field_int(PREADY, UVM_ALL_ON)
	`uvm_field_int(PSLVERR, UVM_ALL_ON)
	`uvm_field_int(PRDATA, UVM_ALL_ON)
	`uvm_object_utils_end

	function new(string name = "apb_slv_seq_item");
		super.new(name);
	endfunction: new

endclass: apb_slv_seq_item

