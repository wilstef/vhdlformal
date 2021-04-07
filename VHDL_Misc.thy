theory vhdl_misc
imports Main vhdl_types
begin

text {* Generate a vector of std_logic values of length n. *}

primrec std_logic_vec_gen:: "nat \<Rightarrow> val \<Rightarrow> val list" where
"std_logic_vec_gen 0 v = []"
|"std_logic_vec_gen (Suc n) v = v#(std_logic_vec_gen n v)"

text {* Our currently treat a record in VHDL as a list of signals/ports/variables. 
We address the members of the record by matching the names of signals/ports/variables 
in the list. *}

text {* First we define null signal/port/variable. *}

definition null_port:: "port" where
"null_port \<equiv> (''NULL'', vhdl_integer, mode_out, unconnected, exp_con (vhdl_integer, val_null))"

definition null_signal:: "signal" where
"null_signal \<equiv> (''NULL'', vhdl_integer, register, (exp_con (vhdl_integer, val_null)))"

definition null_variable:: "variable" where
"null_variable \<equiv> (''NULL'', vhdl_integer, (exp_con (vhdl_integer, val_null)))"

text {* Find a member of the port/signal/variable list by name. *}

primrec port_list_mem:: "port list \<Rightarrow> string \<Rightarrow> port" (infixr "." 65) where
"port_list_mem [] n = null_port"
|"port_list_mem (p#px) n = (if n = (fst p) then p else port_list_mem px n)"

primrec signal_list_mem:: "signal list \<Rightarrow> string \<Rightarrow> signal" (infixr "." 65) where
"signal_list_mem [] n = null_signal"
|"signal_list_mem (s#sx) n = (if n = (fst s) then s else signal_list_mem sx n)"

primrec variable_list_mem:: "variable list \<Rightarrow> string \<Rightarrow> variable" (infixr "." 65) where
"variable_list_mem [] n = null_variable"
|"variable_list_mem (v#vx) n = (if n = (fst v) then v else variable_list_mem vx n)"

end