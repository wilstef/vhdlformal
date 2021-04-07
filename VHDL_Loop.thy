(*
 * Copyright 2016, NTU
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * Author: Zhe Hou.
 *)

theory vhdl_loop
imports Main vhdl_component vhdl_syntax_complex
begin

definition p_input:: "port" where
"p_input \<equiv> 
(''input'', vhdl_natural, mode_in, connected, (exp_con (vhdl_natural, (val_i 12))))"

definition p_output:: "port" where
"p_output \<equiv> 
(''output'', vhdl_natural, mode_out, connected, (exp_con (vhdl_natural, (val_i 0))))"

definition s_sig:: "signal" where
"s_sig \<equiv> (''sig'', vhdl_natural, register, (exp_con (vhdl_natural, (val_i 0))))"

definition v_var:: "variable" where
"v_var \<equiv> (''var'', vhdl_natural, (exp_con (vhdl_natural, (val_i 1))))"

definition vhdl_factorial:: "vhdl_desc_complex" where
"vhdl_factorial \<equiv> 
  let env = \<lparr>env_sp = [sp_p p_input, sp_p p_clk, sp_p p_output, 
                       sp_s s_sig], 
             env_v = [v_var],
             env_t = []\<rparr>; 
      resfn = \<lambda>x. (None);
      cst_list = [
        (''Loop'': PROCESS ([sp_p p_clk]) 
          BEGIN [
            ('''': WHILE (bexpr (exp_sig s_sig) [=] (exp_con (vhdl_natural, (val_i 0))))
              LOOP [
                ('''': (clhs_v (lhs_v v_var)) := (rhs_e (bexpa (exp_var v_var) [*] (exp_con (vhdl_integer, (val_i 2))))))]
              END LOOP)]
          END PROCESS)]
  in
  (env, resfn, cst_list,[])"

export_code vhdl_factorial simulation init_state trans_vhdl_desc_complex in OCaml
module_name vhdl_loop file vhdl_loop

end