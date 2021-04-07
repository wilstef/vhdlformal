(*
 * Copyright 2016, NTU
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * Author: Zhe Hou.
 *)

theory VHDL_Factorial
imports Main vhdl_component vhdl_syntax_complex
begin

definition p_input:: "port" where
"p_input \<equiv> 
(''input'', vhdl_natural, mode_in, connected, (exp_con (vhdl_natural, (val_i 12))))"

definition p_output:: "port" where
"p_output \<equiv> 
(''output'', vhdl_natural, mode_out, connected, (exp_con (vhdl_natural, (val_i 0))))"

definition p_start:: "port" where
"p_start \<equiv> 
(''start'', vhdl_bit, mode_in, connected, (exp_con (vhdl_bit, (val_c (CHR ''1'')))))"

definition p_done:: "port" where  
"p_done \<equiv> 
(''done'', vhdl_bit, mode_out, connected, (exp_con (vhdl_bit, (val_c (CHR ''0'')))))"

definition s_op1:: "signal" where
"s_op1 \<equiv> (''op1'', vhdl_natural, register, (exp_con (vhdl_natural, (val_i 0))))"

definition s_op2:: "signal" where
"s_op2 \<equiv> (''op2'', vhdl_natural, register, (exp_con (vhdl_natural, (val_i 0))))"

definition s_resmult:: "signal" where
"s_resmult \<equiv>  (''resmult'', vhdl_natural, register, (exp_con (vhdl_natural, (val_i 0))))"

definition s_startmult:: "signal" where
"s_startmult \<equiv> (''startmult'', vhdl_bit, register, (exp_con (vhdl_natural, (val_c (CHR ''0'')))))"

definition s_endmult:: "signal" where
"s_endmult \<equiv> (''endmult'', vhdl_bit, register, (exp_con (vhdl_natural, (val_c (CHR ''0'')))))"

definition v_mystate:: "variable" where
"v_mystate \<equiv> (''mystate'', vhdl_natural, (exp_con (vhdl_natural, (val_i 0))))"

definition v_R:: "variable" where
"v_R \<equiv> (''R'', vhdl_natural, (exp_con (vhdl_natural, (val_i 0))))"

definition v_F:: "variable" where
"v_F \<equiv> (''F'', vhdl_natural, (exp_con (vhdl_natural, (val_i 0))))"

definition vhdl_factorial:: "vhdl_desc_complex" where
"vhdl_factorial \<equiv> 
  let env = \<lparr>env_sp = [sp_p p_input, sp_p p_start, sp_p p_clk, sp_p p_output, 
                       sp_p p_done, sp_s s_op1, sp_s s_op2, sp_s s_resmult, 
                       sp_s s_startmult, sp_s s_endmult], 
             env_v = [v_mystate, v_R, v_F],
             env_t = []\<rparr>; 
      resfn = \<lambda>x. (None);
      cst_list = [
        (''Multiplier'': PROCESS ([sp_p p_clk]) 
          BEGIN [
            ('''': IF (bexpr (exp_sig s_startmult) [=] (exp_con (vhdl_bit, (val_c (CHR ''1'')))))
              THEN [
                ('''': (clhs_sp (lhs_s (sp_s s_resmult))) <= (rhs_e (bexpa (exp_sig s_op1) [*] (exp_sig s_op2))))]
              [] ELSE [] END IF),
            ('''': (clhs_sp (lhs_s (sp_s s_endmult))) <= (rhs_e (exp_sig s_startmult)))]
          END PROCESS),
        (''Doit'': PROCESS ([sp_p p_clk])
          BEGIN [
            ('''': IF (bexpr (exp_var v_mystate) [=] (exp_con (vhdl_natural, (val_i 0)))) 
              THEN [
                ('''': (clhs_v (lhs_v v_R)) := (rhs_e (exp_prt p_input))), 
                ('''': (clhs_v (lhs_v v_F)) := (rhs_e (exp_con (vhdl_natural, (val_i 1))))), 
                ('''': IF (bexpr (exp_prt p_start) [=] (exp_con (vhdl_bit, (val_c (CHR ''1''))))) 
                  THEN [
                    ('''': (clhs_v (lhs_v v_mystate)) := (rhs_e (exp_con (vhdl_natural, (val_i 1)))))]
                  [] ELSE [] END IF)]
              [] ELSE [
                ('''': IF (bexpr (exp_var v_mystate) [=] (exp_con (vhdl_natural, (val_i 1)))) 
                  THEN [
                    ('''': IF (bexpr (exp_var v_R) [=] (exp_con (vhdl_natural, (val_i 1))))  
                      THEN [
                        ('''': (clhs_sp (lhs_s (sp_p p_output))) <= (rhs_e (exp_var v_F))),
                        ('''': (clhs_sp (lhs_s (sp_p p_done))) <= (rhs_e (exp_con (vhdl_bit, (val_c (CHR ''1'')))))),
                        ('''': (clhs_v (lhs_v v_mystate)) := (rhs_e (exp_con (vhdl_natural, (val_i 0)))))]
                      [] ELSE [
                        ('''': (clhs_sp (lhs_s (sp_s s_startmult))) <= (rhs_e (exp_con (vhdl_bit, (val_c (CHR ''1'')))))),
                        ('''': (clhs_sp (lhs_s (sp_s s_op1))) <= (rhs_e (exp_var v_R))),
                        ('''': (clhs_sp (lhs_s (sp_s s_op2))) <= (rhs_e (exp_var v_F))),
                        ('''': (clhs_v (lhs_v v_mystate)) := (rhs_e (exp_con (vhdl_natural, (val_i 2)))))]
                      END IF)]
                  [] ELSE [
                    ('''': IF (bexpr (exp_var v_mystate) [=] (exp_con (vhdl_natural, (val_i 2))))
                      THEN [
                        ('''': IF (bexpr (exp_sig s_endmult) [=] (exp_con (vhdl_bit, (val_c (CHR ''1'')))))
                          THEN [
                            ('''': (clhs_v (lhs_v v_F)) := (rhs_e (exp_sig s_resmult))),
                            ('''': (clhs_v (lhs_v v_R)) := (rhs_e (bexpa (exp_var v_R) [-] (exp_con (vhdl_natural, (val_i 1)))))),
                            ('''': (clhs_sp (lhs_s (sp_s s_startmult))) <= (rhs_e (exp_con (vhdl_bit, (val_c (CHR ''0'')))))),
                            ('''': (clhs_v (lhs_v v_mystate)) := (rhs_e (exp_con (vhdl_natural, (val_i 1)))))]
                          [] ELSE [] END IF)]
                      [] ELSE [] END IF)] 
                  END IF)]
              END IF)]
          END PROCESS)]
  in
  (env, resfn, cst_list, [])"

export_code vhdl_factorial simulation init_state trans_vhdl_desc_complex in OCaml
module_name vhdl_factorial file vhdl_factorial

end