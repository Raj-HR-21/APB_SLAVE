class apb_slv_driver extends uvm_driver#(apb_slv_seq_item);
	`uvm_component_utils(apb_slv_driver)
	virtual apb_slv_intf vif;

	function new(string name = "apb_slv_driver", uvm_component parent = null);
		super.new(name, parent);
	endfunction: new
	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		if( !(uvm_config_db#(virtual apb_slv_intf)::get(this, "", "vif", vif) ))
			`uvm_error("DRIVER", "NO VIRTUAL INTERFACE IN DRIVER")
	endfunction: build_phase

	virtual task run_phase(uvm_phase phase);
		vif.drv_cb.PSEL    <= 0;
		vif.drv_cb.PENABLE <= 0;
		repeat(2) @(vif.drv_cb);
		forever begin
			seq_item_port.get_next_item(req);
			drive_task();
			seq_item_port.item_done();
		end
	endtask: run_phase

	task drive_task();
		$display("[%5t] ====DRV============================================================================================== ", $time);
		vif.drv_cb.PSEL	   <= req.PSEL;
		vif.drv_cb.PENABLE <= req.PENABLE;
		vif.drv_cb.PWRITE  <= req.PWRITE;
		vif.drv_cb.PWDATA  <= req.PWDATA;
		vif.drv_cb.PSTRB   <= req.PSTRB;
		vif.drv_cb.PADDR   <= req.PADDR;

		
		`uvm_info("DRV", $sformatf("\nPSEL=%0d | PENABLE=%0d | PWRITE = %0d | PSTRB = %b | PWDATA = %h | PADDR = %0d \n", req.PSEL, req.PENABLE, req.PWRITE, req.PSTRB, req.PWDATA, req.PADDR), UVM_MEDIUM)
		repeat(2) @(vif.drv_cb);
	endtask: drive_task
endclass: apb_slv_driver

