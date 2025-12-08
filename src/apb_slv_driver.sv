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
		// IDLE
		vif.drv_cb.PSEL    <= 0;
		vif.drv_cb.PENABLE <= 0;
		$display("[%5t] ================================================================================================== ", $time);
		// SETUP PHASE
		@(vif.drv_cb);
		//$display($time,"  ----------------setup-----------------------------");
		vif.drv_cb.PSEL    <= 1;
		vif.drv_cb.PENABLE <= 0;
		vif.drv_cb.PWRITE  <= req.PWRITE;
		vif.drv_cb.PADDR   <= req.PADDR;
		vif.drv_cb.PWDATA  <= (req.PWRITE) ? req.PWDATA : 0;
		vif.drv_cb.PSTRB   <= (req.PWRITE) ? req.PSTRB : 0;
		
		// ACCESS PHASE
		@(vif.drv_cb);
		//$display($time,"  ----------------access-----------------------------");
		vif.drv_cb.PSEL    <= 1;
		vif.drv_cb.PENABLE <= 1;

		`uvm_info("DRV", $sformatf("\nPWRITE = %0d | PSTRB = %b | PWDATA = %h | PADDR = %0d \n", req.PWRITE, req.PSTRB, req.PWDATA, req.PADDR), UVM_LOW)

		//while(!vif.drv_cb.PREADY) 
		@(vif.drv_cb);
	endtask: drive_task


endclass: apb_slv_driver

