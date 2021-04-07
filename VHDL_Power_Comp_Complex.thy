(*
 * Copyright 2016, NTU
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * Author: Zhe Hou.
 *)

theory vhdl_power_comp_complex
imports Main vhdl_component vhdl_syntax_complex
begin

definition p_a:: "port" where
"p_a \<equiv> (''A'', vhdl_natural, mode_in, connected, (exp_con (vhdl_natural, (val_i 0))))"

definition p_b:: "port" where
"p_b \<equiv> (''B'', vhdl_natural, mode_in, connected, (exp_con (vhdl_natural, (val_i 0))))"

definition p_req:: "port" where
"p_req \<equiv> 
(''REQ'', vhdl_bit, mode_in, connected, (exp_con (vhdl_bit, (val_c (CHR ''0'')))))"

definition p_prod:: "port" where
"p_prod \<equiv> 
(''PROD'', vhdl_natural, mode_out, connected, (exp_con (vhdl_natural, (val_i 0))))"

definition p_ack:: "port" where  
"p_ack \<equiv> 
(''ACK'', vhdl_bit, mode_out, connected, (exp_con (vhdl_bit, (val_c (CHR ''0'')))))"

definition s_state:: "signal" where
"s_state \<equiv> (''STATE'', vhdl_natural, register, (exp_con (vhdl_natural, (val_i 0))))"

definition s_result:: "signal" where
"s_result \<equiv> (''RESULT'', vhdl_natural, register, (exp_con (vhdl_natural, (val_i 0))))"

definition s_count:: "signal" where
"s_count \<equiv> (''COUNT'', vhdl_natural, register, (exp_con (vhdl_natural, (val_i 0))))"

definition vhdl_mult:: "vhdl_desc_complex" where
"vhdl_mult \<equiv>
  let env = \<lparr>env_sp = [sp_p p_clk, sp_p p_a, sp_p p_b, sp_p p_req, sp_p p_prod, sp_p p_ack,
                       sp_s s_state, sp_s s_result, sp_s s_count
              ],
             env_v = [],
             env_t = []\<rparr>;
      resfn = \<lambda>x.(None);
      cst_list = [
        (''MAIN'': PROCESS ([sp_p p_clk])
          BEGIN [
            ('''': CASE (exp_sig s_state) IS [
              (WHEN [(exp_con (vhdl_natural, (val_i 0)))] =>
              [
                ('''': IF (bexpr (exp_prt p_req) [=] (exp_con (vhdl_bit, (val_c (CHR ''1'')))))
                  THEN [
                    ('''': (clhs_sp (lhs_s (sp_s s_count))) <= (rhs_e (exp_prt p_a))),
                    ('''': (clhs_sp (lhs_s (sp_s s_result))) <= (rhs_e (exp_con (vhdl_natural, (val_i 0))))),
                    ('''': (clhs_sp (lhs_s (sp_s s_state))) <= (rhs_e (exp_con (vhdl_natural, (val_i 1)))))
                  ] []
                  ELSE [] END IF
                )
              ]),
              (WHEN [(exp_con (vhdl_natural, (val_i 1)))] =>
              [
                ('''': IF (bexpr (exp_sig s_count) [=] (exp_con (vhdl_natural, (val_i 0))))
                  THEN [
                    ('''': (clhs_sp (lhs_s (sp_p p_prod))) <= (rhs_e (exp_sig s_result))),
                    ('''': (clhs_sp (lhs_s (sp_p p_ack))) <= (rhs_e (exp_con (vhdl_bit, (val_c (CHR ''1'')))))),
                    ('''': (clhs_sp (lhs_s (sp_s s_state))) <= (rhs_e (exp_con (vhdl_natural, (val_i 2)))))
                  ] []
                  ELSE [
                    ('''': (clhs_sp (lhs_s (sp_s s_result))) <= (rhs_e (bexpa (exp_sig s_result) [+] (exp_prt p_b)))),
                    ('''': (clhs_sp (lhs_s (sp_s s_count))) <= (rhs_e (bexpa (exp_sig s_count) [-] (exp_con (vhdl_natural, (val_i 1))))))
                  ] 
                  END IF
                )
              ]),
              (WHEN [(exp_con (vhdl_natural, (val_i 2)))] =>
              [
                ('''': IF (bexpr (exp_prt p_req) [=] (exp_con (vhdl_bit, (val_c (CHR ''0'')))))
                  THEN [
                    ('''': (clhs_sp (lhs_s (sp_p p_ack))) <= (rhs_e (exp_con (vhdl_bit, (val_c (CHR ''0'')))))),
                    ('''': (clhs_sp (lhs_s (sp_s s_state))) <= (rhs_e (exp_con (vhdl_natural, (val_i 0)))))
                  ] []
                  ELSE [] END IF
                )
              ]) 
            ] WHEN OTHERS => [] END CASE)
          ]
          END PROCESS
        )
      ]
  in
  (env, resfn, cst_list, [])
"

definition p_arg1:: "port" where
"p_arg1 \<equiv> (''arg1'', vhdl_natural, mode_in, connected, (exp_con (vhdl_natural, (val_i 2))))"

definition p_arg2:: "port" where
"p_arg2 \<equiv> (''arg2'', vhdl_natural, mode_in, connected, (exp_con (vhdl_natural, (val_i 12))))"

definition p_start:: "port" where
"p_start \<equiv> 
(''start'', vhdl_bit, mode_in, connected, (exp_con (vhdl_bit, (val_c (CHR ''1'')))))"

definition p_res:: "port" where
"p_res \<equiv> 
(''res'', vhdl_natural, mode_out, connected, (exp_con (vhdl_natural, (val_i 0))))"

definition p_done:: "port" where  
"p_done \<equiv> 
(''done'', vhdl_bit, mode_out, connected, (exp_con (vhdl_bit, (val_c (CHR ''0'')))))"

definition s_reg1:: "signal" where
"s_reg1 \<equiv> (''reg1'', vhdl_natural, register, (exp_con (vhdl_natural, (val_i 0))))"

definition s_reg2:: "signal" where
"s_reg2 \<equiv> (''reg2'', vhdl_natural, register, (exp_con (vhdl_natural, (val_i 0))))"

definition s_req:: "signal" where
"s_req \<equiv> (''req'', vhdl_bit, register, (exp_con (vhdl_bit, (val_c (CHR ''0'')))))"

definition s_ack:: "signal" where
"s_ack \<equiv> (''ack'', vhdl_bit, register, (exp_con (vhdl_bit, (val_c (CHR ''0'')))))"

definition vhdl_power:: "vhdl_desc_complex" where
"vhdl_power \<equiv>
  let env = \<lparr>env_sp = [sp_p p_clk, sp_p p_arg1, sp_p p_arg2, sp_p p_start, sp_p p_res, sp_p p_done,
                       sp_s s_state, sp_s s_reg1, sp_s s_reg2, sp_s s_result, sp_s s_count,
                       sp_s s_req, sp_s s_ack
              ],
             env_v = [],
             env_t = []\<rparr>;
      resfn = \<lambda>x.(None);
      cst_list = [
        (''CONTROLLER'': PROCESS ([sp_p p_clk])
          BEGIN [
            ('''': CASE (exp_sig s_state) IS [ 
              (WHEN [(exp_con (vhdl_natural, (val_i 0)))] =>
                [('''': IF (bexpr (exp_prt p_start) [=] (exp_con (vhdl_bit, (val_c (CHR ''1'')))))
                  THEN [
                    ('''': (clhs_sp (lhs_s (sp_s s_reg1))) <= (rhs_e (exp_prt p_arg1))),
                    ('''': (clhs_sp (lhs_s (sp_s s_reg2))) <= (rhs_e (exp_con (vhdl_natural, (val_i 1))))),
                    ('''': (clhs_sp (lhs_s (sp_s s_count))) <= (rhs_e (exp_prt p_arg2))),
                    ('''': (clhs_sp (lhs_s (sp_s s_state))) <= (rhs_e (exp_con (vhdl_natural, (val_i 1)))))
                  ] []
                  ELSE [] END IF
                )]),
              (WHEN [(exp_con (vhdl_natural, (val_i 1)))] => 
                [('''': IF (bexpr (exp_sig s_count) [=] (exp_con (vhdl_natural, (val_i 0))))
                  THEN [
                    ('''': (clhs_sp (lhs_s (sp_p p_res))) <= (rhs_e (exp_sig s_reg2))),
                    ('''': (clhs_sp (lhs_s (sp_p p_done))) <= (rhs_e (exp_con (vhdl_bit, (val_c (CHR ''1'')))))),
                    ('''': (clhs_sp (lhs_s (sp_s s_state))) <= (rhs_e (exp_con (vhdl_natural, (val_i 4)))))
                  ] []
                  ELSE [
                    ('''': (clhs_sp (lhs_s (sp_s s_req))) <= (rhs_e (exp_con (vhdl_bit, (val_c (CHR ''1'')))))),
                    ('''': (clhs_sp (lhs_s (sp_s s_state))) <= (rhs_e (exp_con (vhdl_natural, (val_i 2)))))
                  ] 
                  END IF
                )]),
              (WHEN [(exp_con (vhdl_natural, (val_i 2)))] =>
                [('''': IF (bexpr (exp_sig s_ack) [=] (exp_con (vhdl_bit, (val_c (CHR ''1'')))))
                  THEN [
                    ('''': (clhs_sp (lhs_s (sp_s s_reg2))) <= (rhs_e (exp_sig s_result))),
                    ('''': (clhs_sp (lhs_s (sp_s s_req))) <= (rhs_e (exp_con (vhdl_bit, (val_c (CHR ''0'')))))),
                    ('''': (clhs_sp (lhs_s (sp_s s_state))) <= (rhs_e (exp_con (vhdl_natural, (val_i 3)))))
                  ] []
                  ELSE [] END IF
                )]),
              (WHEN [(exp_con (vhdl_natural, (val_i 3)))] => 
                [('''': (clhs_sp (lhs_s (sp_s s_count))) <= (rhs_e (bexpa (exp_sig s_count) [-] (exp_con (vhdl_natural, (val_i 1)))))),
                 ('''': (clhs_sp (lhs_s (sp_s s_state))) <= (rhs_e (exp_con (vhdl_natural, (val_i 1)))))
                ]),
              (WHEN [(exp_con (vhdl_natural, (val_i 4)))] => 
                [('''': IF (bexpr (exp_prt p_start) [=] (exp_con (vhdl_bit, (val_c (CHR ''0'')))))
                  THEN [
                    ('''': (clhs_sp (lhs_s (sp_p p_done))) <= (rhs_e (exp_con (vhdl_bit, (val_c (CHR ''0'')))))),
                    ('''': (clhs_sp (lhs_s (sp_s s_state))) <= (rhs_e (exp_con (vhdl_natural, (val_i 1)))))
                  ] []
                  ELSE [] END IF
                )])
              ] WHEN OTHERS => [] END CASE
            )] END PROCESS
        )]
  in
  (env, resfn, cst_list, [])
"

definition vhdl_power_comp:: "vhdl_arch_desc_all" where
"vhdl_power_comp \<equiv> [(''MULT'', trans_vhdl_desc_complex vhdl_mult),
  (''POWER'', trans_vhdl_desc_complex vhdl_power)]"

definition init_arch_state_mult:: "vhdl_arch_state" where
"init_arch_state_mult \<equiv> arch_state (''MULT'',init_state,[])"

definition mult_unit_comp_map:: "comp_port_map" where
"mult_unit_comp_map \<equiv> add_comp_port_map 
  [(sp_p p_a, sp_s s_reg1),(sp_p p_b, sp_s s_reg2),(sp_p p_req, sp_s s_req),
   (sp_p p_clk, sp_p p_clk),(sp_p p_prod, sp_s s_result),(sp_p p_ack, sp_s s_ack)] 
  emp_comp_port_map
"

definition init_arch_state_power:: "vhdl_arch_state" where
"init_arch_state_power \<equiv> arch_state (''POWER'',init_state,
  [(mult_unit_comp_map,init_arch_state_mult)])"

export_code vhdl_power_comp init_arch_state_power sim_arch in OCaml
module_name vhdl_power_comp_complex file vhdl_power_comp_complex

end