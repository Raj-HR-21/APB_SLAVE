class apb_slv_sequence extends uvm_sequence#(apb_slv_seq_item);
	`uvm_object_utils(apb_slv_sequence)

	function new(string name = "apb_slv_sequence");
		super.new(name);
	endfunction: new

	task body();
		repeat(10) begin
			req = apb_slv_seq_item::type_id::create("req");
			wait_for_grant();
			assert(req.randomize());
			send_request(req);
			wait_for_item_done();
		end
	endtask: body

endclass: apb_slv_sequence
////////////////////////////////////////////////////////////
//-------- only write -------- 
class write_seq extends uvm_sequence#(apb_slv_seq_item);
	`uvm_object_utils(write_seq)
	function new(string name = "write_seq");
		super.new(name);
	endfunction
	task body();
			`uvm_do_with(req, {req.PSEL == 0; req.PENABLE == 0;})
			`uvm_do_with(req, {req.PSEL == 1; req.PENABLE == 0; req.PWRITE == 1; req.PSTRB == 4'b1111;})
		repeat(10) begin
			`uvm_do_with(req, {req.PSEL == 1; req.PENABLE == 1; req.PWRITE == 1; req.PSTRB == 4'b1111;})
		end
	endtask: body
endclass: write_seq
////////////////////////////////////////////////////////////
//-------- only read  -------- 
class read_seq extends uvm_sequence#(apb_slv_seq_item);
	`uvm_object_utils(read_seq)
	function new(string name = "read_seq");
		super.new(name);
	endfunction
	task body();
			`uvm_do_with(req, {req.PSEL == 0; req.PENABLE == 0;})
			`uvm_do_with(req, {req.PSEL == 1; req.PENABLE == 0; req.PWRITE == 0;})
		repeat(10) begin
			`uvm_do_with(req, {req.PSEL == 1; req.PENABLE == 1; req.PWRITE == 0;})
		end
	endtask: body
endclass: read_seq
////////////////////////////////////////////////////////////
//-------- random address write and read -------- 
class random_write_read_seq extends uvm_sequence#(apb_slv_seq_item);
	`uvm_object_utils(random_write_read_seq)
	function new(string name = "random_write_read_seq");
		super.new(name);
	endfunction
	task body();
			`uvm_do_with(req, {req.PSEL == 0; req.PENABLE == 0;})
			`uvm_do_with(req, {req.PSEL == 1; req.PENABLE == 0; req.PWRITE == 1; req.PSTRB == 4'b1111; req.PADDR inside {[0:255]};})
		repeat(100) begin
			//write
			`uvm_do_with(req, {req.PSEL == 1; req.PENABLE == 1; req.PWRITE == 1; req.PSTRB == 4'b1111; req.PADDR inside {[0:255]};})
			//read
		//	`uvm_do_with(req, {req.PSEL == 1; req.PENABLE == 0; req.PWRITE == 0;})
			`uvm_do_with(req, {req.PSEL == 1; req.PENABLE == 1; req.PWRITE == 0;})
		end
	endtask
endclass: random_write_read_seq
////////////////////////////////////////////////////////////
//-------- write and read from same address -------- 
class write_then_read_seq extends uvm_sequence#(apb_slv_seq_item);
	`uvm_object_utils(write_then_read_seq)
	bit [`AW-1 :0] addr;
	function new(string name = "write_then_read_seq");
		super.new(name);
	endfunction
	task body();
			`uvm_do_with(req, {req.PSEL == 0; req.PENABLE == 0;})
			`uvm_do_with(req, {req.PSEL == 1; req.PENABLE == 0; req.PWRITE == 1; req.PSTRB == 4'b1111; req.PADDR inside {[0:255]};})
		repeat(10) begin
			//write
			`uvm_do_with(req, {req.PSEL == 1; req.PENABLE == 1; req.PWRITE == 1; req.PSTRB == 4'b1111; req.PADDR inside {[0:255]};})
			addr = req.PADDR;
			//read
		//	`uvm_do_with(req, {req.PSEL == 0; req.PENABLE == 0;})
		//	`uvm_do_with(req, {req.PSEL == 1; req.PENABLE == 0; req.PWRITE == 0;})
			`uvm_do_with(req, {req.PSEL == 1; req.PENABLE == 1; req.PWRITE == 0;req.PADDR == addr;})
		end
	endtask
endclass: write_then_read_seq
////////////////////////////////////////////////////////////
//-------- first write continuously then continuous read -------- 
class write_then_read_seq2 extends uvm_sequence#(apb_slv_seq_item);
        `uvm_object_utils(write_then_read_seq2)
        bit [`AW-1 :0] addr;
        function new(string name = "write_then_read_seq2");
                super.new(name);
        endfunction
        task body();
			`uvm_do_with(req, {req.PSEL == 0; req.PENABLE == 0;})
			`uvm_do_with(req, {req.PSEL == 1; req.PENABLE == 0; req.PWRITE == 1; req.PSTRB == 4'b1111;})
		for(int i = 0; i < 100; i=i+10) begin
			`uvm_do_with(req, {req.PSEL == 1; req.PENABLE == 1; req.PWRITE == 1; req.PSTRB == 4'b1111; req.PADDR == i;})
                end
		for(int i = 0; i < 100; i=i+10) begin
			`uvm_do_with(req, {req.PSEL == 1; req.PENABLE == 1; req.PWRITE == 0; req.PSTRB == 4'b1111; req.PADDR == i;})
                end
        endtask

endclass: write_then_read_seq2
////////////////////////////////////////////////////////////
//-------- partial byte write with PSTRB and read from same address -------- 
class write_partial_bytes_seq extends uvm_sequence#(apb_slv_seq_item);
	`uvm_object_utils(write_partial_bytes_seq)
	bit [`AW-1 :0] addr;
	function new(string name = "write_partial_bytes_seq");
		super.new(name);
	endfunction
	task body();
			`uvm_do_with(req, {req.PSEL == 0; req.PENABLE == 0;})
			`uvm_do_with(req, {req.PSEL == 1; req.PENABLE == 0; req.PWRITE == 1; req.PSTRB == 4'b1111;})
		repeat(5) begin
			`uvm_do_with(req, {req.PSEL == 1; req.PENABLE == 1; req.PWRITE == 1; req.PSTRB inside {[1:14]}; req.PADDR inside {[0:255]};})
			addr = req.PADDR;
			`uvm_do_with(req, {req.PSEL == 1; req.PENABLE == 1; req.PWRITE == 0; req.PADDR == addr;})

		end
	endtask

endclass: write_partial_bytes_seq
////////////////////////////////////////////////////////////
//-------- Overwrite with different PSTRB patterns --------
class overwrite_with_strb_seq extends uvm_sequence#(apb_slv_seq_item);
	`uvm_object_utils(overwrite_with_strb_seq)
	bit [`AW-1 :0] addr;
	function new(string name = "overwrite_with_strb_seq");
		super.new(name);
	endfunction
	task body();
			`uvm_do_with(req, {req.PSEL == 0; req.PENABLE == 0;})
			`uvm_do_with(req, {req.PSEL == 1; req.PENABLE == 0; req.PWRITE == 1; req.PSTRB == 4'b1111;})
		repeat(5) begin
			`uvm_do_with(req, {req.PSEL == 1; req.PENABLE == 1; req.PWRITE == 1; req.PSTRB == 4'b1111; req.PADDR inside {[0:255]};})
			addr = req.PADDR;
			`uvm_do_with(req, {req.PSEL == 1; req.PENABLE == 1; req.PWRITE == 1; req.PADDR == addr; req.PSTRB inside {[1:14]};})
			`uvm_do_with(req, {req.PSEL == 1; req.PENABLE == 1; req.PWRITE == 0; req.PADDR == addr;})
		end
	endtask
endclass: overwrite_with_strb_seq
////////////////////////////////////////////////////////////
//-------- No strobe for write --------
class no_pstrb_seq extends uvm_sequence#(apb_slv_seq_item);
	`uvm_object_utils(no_pstrb_seq)
	bit [`AW-1 :0] addr;
	function new(string name = "no_pstrb_seq");
		super.new(name);
	endfunction
	task body();
			`uvm_do_with(req, {req.PSEL == 0; req.PENABLE == 0;})
			`uvm_do_with(req, {req.PSEL == 1; req.PENABLE == 0; req.PWRITE == 1; req.PSTRB == 4'b1111;})
		repeat(5) begin
			`uvm_do_with(req, {req.PSEL == 1; req.PENABLE == 1; req.PWRITE == 1; req.PSTRB == 4'b0; req.PADDR inside {[0:255]};})
			addr = req.PADDR;
			`uvm_do_with(req, {req.PSEL == 1; req.PENABLE == 1; req.PWRITE == 0; req.PADDR == addr;})
		end
	endtask
endclass: no_pstrb_seq
////////////////////////////////////////////////////////////
//-------- write to location byte wise --------
class byte_wise_write_seq extends uvm_sequence#(apb_slv_seq_item);
	`uvm_object_utils(byte_wise_write_seq)
	bit [`AW-1 :0] addr;
	function new(string name = "byte_wise_write_seq");
		super.new(name);
	endfunction
	task body();
			`uvm_do_with(req, {req.PSEL == 0; req.PENABLE == 0;})
			`uvm_do_with(req, {req.PSEL == 1; req.PENABLE == 0; req.PWRITE == 1; req.PSTRB == 4'b1111;})
		repeat(5) begin
			`uvm_do_with(req, {req.PSEL == 1; req.PENABLE == 1; req.PWRITE == 1; req.PSTRB == 4'b0001; req.PADDR inside {[0:255]};})
			addr = req.PADDR;
			`uvm_do_with(req, {req.PSEL == 1; req.PENABLE == 1; req.PWRITE == 1; req.PSTRB == 4'b0010; req.PADDR == addr;})
			`uvm_do_with(req, {req.PSEL == 1; req.PENABLE == 1; req.PWRITE == 1; req.PSTRB == 4'b0100; req.PADDR == addr;})
			`uvm_do_with(req, {req.PSEL == 1; req.PENABLE == 1; req.PWRITE == 1; req.PSTRB == 4'b1000; req.PADDR == addr;})
			`uvm_do_with(req, {req.PSEL == 1; req.PENABLE == 1; req.PWRITE == 0; req.PADDR == addr;})
		end
	endtask
endclass: byte_wise_write_seq
////////////////////////////////////////////////////////////
//-------- invalid address --------
class invalid_addr_seq extends uvm_sequence#(apb_slv_seq_item);
	`uvm_object_utils(invalid_addr_seq)
	function new(string name = "invalid_addr_seq");
		super.new(name);
	endfunction
	task body();
			`uvm_do_with(req, {req.PSEL == 0; req.PENABLE == 0;})
			`uvm_do_with(req, {req.PSEL == 1; req.PENABLE == 0; req.PWRITE == 1; req.PSTRB == 4'b1111;})
		repeat(500) begin
			`uvm_do_with(req, {req.PSEL == 1; req.PENABLE == 1; req.PWRITE dist {1:=50, 0:=50}; req.PADDR dist{[0:255]:/60, [255:$]:/40};})
		end
	endtask
endclass: invalid_addr_seq
////////////////////////////////////////////////////////////
class regression_seq extends uvm_sequence#(apb_slv_seq_item);
	`uvm_object_utils(regression_seq)

	apb_slv_sequence s0; // base sequence
	write_seq s1;
	read_seq s2;
	random_write_read_seq s3;
	write_then_read_seq s4;
	write_then_read_seq s5;

	write_partial_bytes_seq s6;
	overwrite_with_strb_seq s7;
	no_pstrb_seq s8;
	byte_wise_write_seq s9;
	invalid_addr_seq s10;
	
	function new(string name = "regression_seq");
		super.new(name);
	endfunction
	task body();
		repeat(20) begin
			`uvm_do(s0)
			`uvm_do(s1)
			`uvm_do(s2)
			`uvm_do(s3)
			`uvm_do(s4)
			`uvm_do(s5)
			`uvm_do(s6)
			`uvm_do(s7)
			`uvm_do(s8)
			`uvm_do(s9)
			`uvm_do(s10)
		end
	endtask
endclass: regression_seq 

////////////////////////////////////////////////////////////

