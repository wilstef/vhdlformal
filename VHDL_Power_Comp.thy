(*
 * Copyright 2016, NTU
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * Author: Zhe Hou.
 *)

theory VHDL_Power_Comp
imports Main VHDL_Component VHDL_Syntax_Complex
begin

definition p_a_pc:: "port" where
"p_a_pc \<equiv> (''A'', vhdl_natural, mode_in, connected, (exp_con (vhdl_natural, (val_i 0))))"

definition p_b_pc:: "port" where
"p_b_pc \<equiv> (''B'', vhdl_natural, mode_in, connected, (exp_con (vhdl_natural, (val_i 0))))"

definition p_req_pc:: "port" where
"p_req_pc \<equiv> 
(''REQ'', vhdl_bit, mode_in, connected, (exp_con (vhdl_bit, (val_c (CHR ''0'')))))"

definition p_prod_pc:: "port" where
"p_prod_pc \<equiv> 
(''PROD'', vhdl_natural, mode_out, connected, (exp_con (vhdl_natural, (val_i 0))))"

definition p_ack_pc:: "port" where  
"p_ack_pc \<equiv> 
(''ACK'', vhdl_bit, mode_out, connected, (exp_con (vhdl_bit, (val_c (CHR ''0'')))))"

definition s_state_pc:: "signal" where
"s_state_pc \<equiv> (''STATE'', vhdl_natural, register, (exp_con (vhdl_natural, (val_i 0))))"

definition s_result_pc:: "signal" where
"s_result_pc \<equiv> (''RESULT'', vhdl_natural, register, (exp_con (vhdl_natural, (val_i 0))))"

definition s_count_pc:: "signal" where
"s_count_pc \<equiv> (''COUNT'', vhdl_natural, register, (exp_con (vhdl_natural, (val_i 0))))"

definition vhdl_mult:: "vhdl_desc_complex" where
"vhdl_mult \<equiv>
  let env = \<lparr>env_sp = [sp_p p_clk, sp_p p_a_pc, sp_p p_b_pc, sp_p p_req_pc, sp_p p_prod_pc, sp_p p_ack_pc,
                       sp_s s_state_pc, sp_s s_result_pc, sp_s s_count_pc
              ],
             env_v = [],
             env_t = []\<rparr>;
      resfn = \<lambda>x.(None);
      cst_list = [
        (''MAIN'': PROCESS ([sp_p p_clk])
          BEGIN [
            ('''': IF (bexpr (exp_sig s_state_pc) [=] (exp_con (vhdl_natural, (val_i 0))))
              THEN [
                ('''': IF (bexpr (exp_prt p_req_pc) [=] (exp_con (vhdl_bit, (val_c (CHR ''1'')))))
                  THEN [
                    ('''': (clhs_sp (lhs_s (sp_s s_count_pc))) <= (rhs_e (exp_prt p_a_pc))),
                    ('''': (clhs_sp (lhs_s (sp_s s_result_pc))) <= (rhs_e (exp_con (vhdl_natural, (val_i 0))))),
                    ('''': (clhs_sp (lhs_s (sp_s s_state_pc))) <= (rhs_e (exp_con (vhdl_natural, (val_i 1)))))
                  ]
                  [] ELSE [] END IF
                )
              ]
              [] ELSE [
                ('''': IF (bexpr (exp_sig s_state_pc) [=] (exp_con (vhdl_natural, (val_i 1))))
                  THEN [
                    ('''': IF (bexpr (exp_sig s_count_pc) [=] (exp_con (vhdl_natural, (val_i 0))))
                      THEN [
                        ('''': (clhs_sp (lhs_s (sp_p p_prod_pc))) <= (rhs_e (exp_sig s_result_pc))),
                        ('''': (clhs_sp (lhs_s (sp_p p_ack_pc))) <= (rhs_e (exp_con (vhdl_bit, (val_c (CHR ''1'')))))),
                        ('''': (clhs_sp (lhs_s (sp_s s_state_pc))) <= (rhs_e (exp_con (vhdl_natural, (val_i 2)))))
                      ]
                      [] ELSE [
                        ('''': (clhs_sp (lhs_s (sp_s s_result_pc))) <= (rhs_e (bexpa (exp_sig s_result_pc) [+] (exp_prt p_b_pc)))),
                        ('''': (clhs_sp (lhs_s (sp_s s_count_pc))) <= (rhs_e (bexpa (exp_sig s_count_pc) [-] (exp_con (vhdl_natural, (val_i 1))))))
                      ] 
                      END IF
                    )
                  ]
                  [] ELSE [
                    ('''': IF (bexpr (exp_sig s_state_pc) [=] (exp_con (vhdl_natural, (val_i 2))))
                      THEN [
                        ('''': IF (bexpr (exp_prt p_req_pc) [=] (exp_con (vhdl_bit, (val_c (CHR ''0'')))))
                          THEN [
                            ('''': (clhs_sp (lhs_s (sp_p p_ack_pc))) <= (rhs_e (exp_con (vhdl_bit, (val_c (CHR ''0'')))))),
                            ('''': (clhs_sp (lhs_s (sp_s s_state_pc))) <= (rhs_e (exp_con (vhdl_natural, (val_i 0)))))
                          ]
                          [] ELSE [] END IF
                        )
                      ] 
                      [] ELSE [] END IF
                    )
                  ] END IF
                )
              ] END IF
            )
          ]
          END PROCESS
        )
      ]
  in
  (env, resfn, cst_list,[])
"

definition p_arg1_pc:: "port" where
"p_arg1_pc \<equiv> (''arg1'', vhdl_natural, mode_in, connected, (exp_con (vhdl_natural, (val_i 8))))"

definition p_arg2_pc:: "port" where
"p_arg2_pc \<equiv> (''arg2'', vhdl_natural, mode_in, connected, (exp_con (vhdl_natural, (val_i 3))))"

definition p_start_pc:: "port" where
"p_start_pc \<equiv> 
(''start'', vhdl_bit, mode_in, connected, (exp_con (vhdl_bit, (val_c (CHR ''1'')))))"

definition p_res_pc:: "port" where
"p_res_pc \<equiv> 
(''res'', vhdl_natural, mode_out, connected, (exp_con (vhdl_natural, (val_i 0))))"

definition p_done_pc:: "port" where  
"p_done_pc \<equiv> 
(''done'', vhdl_bit, mode_out, connected, (exp_con (vhdl_bit, (val_c (CHR ''0'')))))"

definition s_reg1_pc:: "signal" where
"s_reg1_pc \<equiv> (''reg1'', vhdl_natural, register, (exp_con (vhdl_natural, (val_i 0))))"

definition s_reg2_pc:: "signal" where
"s_reg2_pc \<equiv> (''reg2'', vhdl_natural, register, (exp_con (vhdl_natural, (val_i 0))))"

definition s_req_pc:: "signal" where
"s_req_pc \<equiv> (''req'', vhdl_bit, register, (exp_con (vhdl_bit, (val_c (CHR ''0'')))))"

definition s_ack_pc:: "signal" where
"s_ack_pc \<equiv> (''ack'', vhdl_bit, register, (exp_con (vhdl_bit, (val_c (CHR ''0'')))))"

definition vhdl_power:: "vhdl_desc_complex" where
"vhdl_power \<equiv>
  let env = \<lparr>env_sp = [sp_p p_clk, sp_p p_arg1_pc, sp_p p_arg2_pc, sp_p p_start_pc, sp_p p_res_pc, sp_p p_done_pc,
                       sp_s s_state_pc, sp_s s_reg1_pc, sp_s s_reg2_pc, sp_s s_result_pc, sp_s s_count_pc,
                       sp_s s_req_pc, sp_s s_ack_pc
              ],
             env_v = [],
             env_t = []\<rparr>;
      resfn = \<lambda>x.(None);
      cst_list = [
        (''CONTROLLER'': PROCESS ([sp_p p_clk])
          BEGIN [
            ('''': IF (bexpr (exp_sig s_state_pc) [=] (exp_con (vhdl_natural, (val_i 0))))
              THEN [
                ('''': IF (bexpr (exp_prt p_start_pc) [=] (exp_con (vhdl_bit, (val_c (CHR ''1'')))))
                  THEN [
                    ('''': (clhs_sp (lhs_s (sp_s s_reg1_pc))) <= (rhs_e (exp_prt p_arg1_pc))),
                    ('''': (clhs_sp (lhs_s (sp_s s_reg2_pc))) <= (rhs_e (exp_con (vhdl_natural, (val_i 1))))),
                    ('''': (clhs_sp (lhs_s (sp_s s_count_pc))) <= (rhs_e (exp_prt p_arg2_pc))),
                    ('''': (clhs_sp (lhs_s (sp_s s_state_pc))) <= (rhs_e (exp_con (vhdl_natural, (val_i 1)))))
                  ]
                  [] ELSE [] END IF
                )
              ]
              [] ELSE [
                ('''': IF (bexpr (exp_sig s_state_pc) [=] (exp_con (vhdl_natural, (val_i 1))))
                  THEN [
                    ('''': IF (bexpr (exp_sig s_count_pc) [=] (exp_con (vhdl_natural, (val_i 0))))
                      THEN [
                        ('''': (clhs_sp (lhs_s (sp_p p_res_pc))) <= (rhs_e (exp_sig s_reg2_pc))),
                        ('''': (clhs_sp (lhs_s (sp_p p_done_pc))) <= (rhs_e (exp_con (vhdl_bit, (val_c (CHR ''1'')))))),
                        ('''': (clhs_sp (lhs_s (sp_s s_state_pc))) <= (rhs_e (exp_con (vhdl_natural, (val_i 4)))))
                      ]
                      [] ELSE [
                        ('''': (clhs_sp (lhs_s (sp_s s_req_pc))) <= (rhs_e (exp_con (vhdl_bit, (val_c (CHR ''1'')))))),
                        ('''': (clhs_sp (lhs_s (sp_s s_state_pc))) <= (rhs_e (exp_con (vhdl_natural, (val_i 2)))))
                      ] 
                      END IF
                    )
                  ]
                  [] ELSE [
                    ('''': IF (bexpr (exp_sig s_state_pc) [=] (exp_con (vhdl_natural, (val_i 2))))
                      THEN [
                        ('''': IF (bexpr (exp_sig s_ack_pc) [=] (exp_con (vhdl_bit, (val_c (CHR ''1'')))))
                          THEN [
                            ('''': (clhs_sp (lhs_s (sp_s s_reg2_pc))) <= (rhs_e (exp_sig s_result_pc))),
                            ('''': (clhs_sp (lhs_s (sp_s s_req_pc))) <= (rhs_e (exp_con (vhdl_bit, (val_c (CHR ''0'')))))),
                            ('''': (clhs_sp (lhs_s (sp_s s_state_pc))) <= (rhs_e (exp_con (vhdl_natural, (val_i 3)))))
                          ]
                          [] ELSE [] END IF
                        )
                      ]
                      [] ELSE [
                        ('''': IF (bexpr (exp_sig s_state_pc) [=] (exp_con (vhdl_natural, (val_i 3))))
                          THEN [
                            ('''': (clhs_sp (lhs_s (sp_s s_count_pc))) <= (rhs_e (bexpa (exp_sig s_count_pc) [-] (exp_con (vhdl_natural, (val_i 1)))))),
                            ('''': (clhs_sp (lhs_s (sp_s s_state_pc))) <= (rhs_e (exp_con (vhdl_natural, (val_i 1)))))
                          ]
                          [] ELSE [
                            ('''': IF (bexpr (exp_sig s_state_pc) [=] (exp_con (vhdl_natural, (val_i 4))))
                              THEN [
                                ('''': IF (bexpr (exp_prt p_start_pc) [=] (exp_con (vhdl_bit, (val_c (CHR ''0'')))))
                                  THEN [
                                    ('''': (clhs_sp (lhs_s (sp_p p_done_pc))) <= (rhs_e (exp_con (vhdl_bit, (val_c (CHR ''0'')))))),
                                    ('''': (clhs_sp (lhs_s (sp_s s_state_pc))) <= (rhs_e (exp_con (vhdl_natural, (val_i 1)))))
                                  ]
                                  [] ELSE [] END IF
                                )
                              ]
                              [] ELSE [] END IF
                            )
                          ] END IF
                        )
                      ] END IF
                    )
                  ] END IF
                )
              ] END IF
            )
          ]
          END PROCESS
        )
      ]
  in
  (env, resfn, cst_list, [])
"

definition vhdl_power_comp:: "vhdl_arch_desc_all" where
"vhdl_power_comp \<equiv> [(''MULT'',trans_vhdl_desc_complex vhdl_mult),(''POWER'',trans_vhdl_desc_complex vhdl_power)]"

definition init_arch_state_mult:: "vhdl_arch_state" where
"init_arch_state_mult \<equiv> arch_state (''MULT'',init_state,[])"

definition mult_unit_comp_map:: "comp_port_map" where
"mult_unit_comp_map \<equiv> add_comp_port_map 
  [(sp_p p_a_pc, sp_s s_reg1_pc),(sp_p p_b_pc, sp_s s_reg2_pc),(sp_p p_req_pc, sp_s s_req_pc),
   (sp_p p_clk, sp_p p_clk),(sp_p p_prod_pc, sp_s s_result_pc),(sp_p p_ack_pc, sp_s s_ack_pc)] 
  emp_comp_port_map
"

definition init_arch_state_power:: "vhdl_arch_state" where
"init_arch_state_power \<equiv> arch_state (''POWER'',init_state,
  [(mult_unit_comp_map,init_arch_state_mult)])"

export_code vhdl_power_comp init_arch_state_power sim_arch trans_vhdl_desc_complex in OCaml
module_name vhdl_power_comp file vhdl_power_comp

end