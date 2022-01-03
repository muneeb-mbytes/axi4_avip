`ifndef AXI4_BASE_TEST_INCLUDED_
`define AXI4_BASE_TEST_INCLUDED_

//--------------------------------------------------------------------------------------------
// Class: axi4_base_test
// axi4_base test has the test scenarios for testbench which has the env, config, etc.
// Sequences are created and started in the test
//--------------------------------------------------------------------------------------------
class axi4_base_test extends uvm_test;
  
  `uvm_component_utils(axi4_base_test)

  // Variable: e_cfg_h
  // Declaring environment config handle
  axi4_env_config axi4_env_cfg_h;

  // Variable: axi4_env_h
  // Handle for environment 
  axi4_env axi4_env_h;

  //-------------------------------------------------------
  // Externally defined Tasks and Functions
  //-------------------------------------------------------
  extern function new(string name = "axi4_base_test", uvm_component parent = null);
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual function void setup_axi4_env_cfg();
  extern virtual function void setup_axi4_master_agent_cfg();
  extern virtual function void setup_axi4_slave_agent_cfg();
  extern virtual function void end_of_elaboration_phase(uvm_phase phase);

endclass : axi4_base_test

//--------------------------------------------------------------------------------------------
// Construct: new
//  Initializes class object
//
// Parameters:
//  name - axi4_base_test
//  parent - parent under which this component is created
//--------------------------------------------------------------------------------------------
function axi4_base_test::new(string name = "axi4_base_test",uvm_component parent = null);
  super.new(name, parent);
endfunction : new

//--------------------------------------------------------------------------------------------
// Function: build_phase
//  Create required ports
//
// Parameters:
//  phase - uvm phase
//--------------------------------------------------------------------------------------------
function void axi4_base_test::build_phase(uvm_phase phase);
  super.build_phase(phase);
  
  // Setup the environemnt cfg 
  setup_axi4_env_cfg();

  // Create the environment
  axi4_env_h = axi4_env::type_id::create("axi4_env_h",this);

endfunction : build_phase


//--------------------------------------------------------------------------------------------
// Function: setup_axi4_env_cfg
// Setup the environment configuration with the required values
// and store the handle into the config_db
//--------------------------------------------------------------------------------------------
function void axi4_base_test:: setup_axi4_env_cfg();
  
  axi4_env_cfg_h = axi4_env_config::type_id::create("axi4_env_cfg_h");

 // axi4_env_cfg_h = axi4_env_config::type_id::create("axi4_env_cfg_h");
 
  axi4_env_cfg_h.has_scoreboard = 1;
  axi4_env_cfg_h.has_virtual_seqr = 1;
  axi4_env_cfg_h.no_of_masters = NO_OF_MASTERS;
  axi4_env_cfg_h.no_of_slaves = NO_OF_SLAVES;

  // Setup the axi4_master agent cfg 
  setup_axi4_master_agent_cfg();
  //Setting the master agent configuration into config_db
  //uvm_config_db#(axi4_master_agent_config)::set(this,"*master_agent*","axi4_master_agent_config",axi4_env_cfg_h.axi4_master_agent_cfg_h);
  //Displaying the master agent configuration
  //`uvm_info(get_type_name(),$sformatf("\nAXI4_MASTER_AGENT_CONFIG\n%s",axi4_env_cfg_h.axi4_master_agent_cfg_h.sprint()),UVM_LOW);


  setup_axi4_slave_agent_cfg();


  // set method for axi4_env_cfg
  uvm_config_db #(axi4_env_config)::set(this,"*","axi4_env_config",axi4_env_cfg_h);
 // `uvm_info(get_type_name(),$sformatf("\nAXI4_ENV_CONFIG\n%s",axi4_env_cfg_h.sprint()),UVM_LOW);

endfunction: setup_axi4_env_cfg

//--------------------------------------------------------------------------------------------
// Function: setup_axi4_master_agent_cfg
// Setup the axi4_master agent configuration with the required values
// and store the handle into the config_db
//--------------------------------------------------------------------------------------------
function void axi4_base_test::setup_axi4_master_agent_cfg();
  bit [63:0]local_min_address;
  bit [63:0]local_max_address;
  axi4_env_cfg_h.axi4_master_agent_cfg_h = new[axi4_env_cfg_h.no_of_masters];
  foreach(axi4_env_cfg_h.axi4_master_agent_cfg_h[i])begin
    axi4_env_cfg_h.axi4_master_agent_cfg_h[i] =
    axi4_master_agent_config::type_id::create("axi4_master_agent_cfg_h");
    axi4_env_cfg_h.axi4_master_agent_cfg_h[i].is_active   = uvm_active_passive_enum'(UVM_ACTIVE);
    axi4_env_cfg_h.axi4_master_agent_cfg_h[i].has_coverage = 1; 
    uvm_config_db#(axi4_master_agent_config)::set(this,"*axi4_master_agent*","axi4_master_agent_config",axi4_env_cfg_h.axi4_master_agent_cfg_h[i]);
  end


  for(int i =0; i<NO_OF_SLAVES; i++) begin
    if(i == 0) begin  
      axi4_env_cfg_h.axi4_master_agent_cfg_h[i].master_min_addr_range(i,0);
      local_min_address = axi4_env_cfg_h.axi4_master_agent_cfg_h[i].master_min_addr_range_array[i];
      
      axi4_env_cfg_h.axi4_master_agent_cfg_h[i].master_max_addr_range(i,2**(SLAVE_MEMORY_SIZE)-1 );
      local_max_address = axi4_env_cfg_h.axi4_master_agent_cfg_h[i].master_max_addr_range_array[i];
    end
    else begin
      axi4_env_cfg_h.axi4_master_agent_cfg_h[i].master_min_addr_range(i,local_max_address + SLAVE_MEMORY_GAP);
      local_min_address = axi4_env_cfg_h.axi4_master_agent_cfg_h[i].master_min_addr_range_array[i];
      
      axi4_env_cfg_h.axi4_master_agent_cfg_h[i].master_max_addr_range(i,local_max_address+ 2**(SLAVE_MEMORY_SIZE)-1 + SLAVE_MEMORY_GAP);
      local_max_address = axi4_env_cfg_h.axi4_master_agent_cfg_h[i].master_max_addr_range_array[i];
    end
  end

endfunction: setup_axi4_master_agent_cfg

//--------------------------------------------------------------------------------------------
// Function: setup_axi4_slave_agents_cfg
// Setup the axi4_slave agent(s) configuration with the required values
// and store the handle into the config_db
//--------------------------------------------------------------------------------------------
function void axi4_base_test::setup_axi4_slave_agent_cfg();
  axi4_env_cfg_h.axi4_slave_agent_cfg_h = new[axi4_env_cfg_h.no_of_slaves];
  foreach(axi4_env_cfg_h.axi4_slave_agent_cfg_h[i])begin
    axi4_env_cfg_h.axi4_slave_agent_cfg_h[i] =
    axi4_slave_agent_config::type_id::create("axi4_slave_agent_cfg_h");
    axi4_env_cfg_h.axi4_slave_agent_cfg_h[i].min_address = axi4_env_cfg_h.axi4_master_agent_cfg_h[i].master_min_addr_range_array[i];
    axi4_env_cfg_h.axi4_slave_agent_cfg_h[i].max_address = axi4_env_cfg_h.axi4_master_agent_cfg_h[i].master_max_addr_range_array[i];
    axi4_env_cfg_h.axi4_slave_agent_cfg_h[i].is_active = uvm_active_passive_enum'(UVM_ACTIVE);
    axi4_env_cfg_h.axi4_slave_agent_cfg_h[i].has_coverage = 1; 
    uvm_config_db #(axi4_slave_agent_config)::set(this,$sformatf("*axi4_slave_agent_h[%0d]*",i),
                                             "axi4_slave_agent_config", axi4_env_cfg_h.axi4_slave_agent_cfg_h[i]);   
   `uvm_info(get_type_name(),$sformatf("\nAXI4_SLAVE_CONFIG[%0d]\n%s",i,axi4_env_cfg_h.axi4_slave_agent_cfg_h[i].sprint()),UVM_LOW);
  end
endfunction: setup_axi4_slave_agent_cfg

//--------------------------------------------------------------------------------------------
// Function: end_of_elaboration_phase
// Used for printing the testbench topology
//
// Parameters:
//  phase - uvm phase
//--------------------------------------------------------------------------------------------
function void axi4_base_test::end_of_elaboration_phase(uvm_phase phase);
  uvm_top.print_topology();
endfunction : end_of_elaboration_phase

`endif

