(*
 * Copyright 2016, NTU
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * Author: Zhe Hou.
 *)

theory VHDL_Power
imports Main VHDL_Component VHDL_Syntax_Complex
begin

definition p_arg1_p:: "port" where
"p_arg1_p \<equiv> (''arg1'', vhdl_natural, mode_in, connected, (exp_con (vhdl_natural, (val_i 4))))"

definition p_arg2_p:: "port" where
"p_arg2_p \<equiv> (''arg2'', vhdl_natural, mode_in, connected, (exp_con (vhdl_natural, (val_i 7))))"

definition p_start_p:: "port" where
"p_start_p \<equiv> 
(''start'', vhdl_bit, mode_in, connected, (exp_con (vhdl_bit, (val_c (CHR ''1'')))))"

definition p_res_p:: "port" where
"p_res_p \<equiv> 
(''res'', vhdl_natural, mode_out, connected, (exp_con (vhdl_natural, (val_i 0))))"

definition p_done_p:: "port" where  
"p_done_p \<equiv> 
(''done'', vhdl_bit, mode_out, connected, (exp_con (vhdl_bit, (val_c (CHR ''0'')))))"

definition s_state_p:: "signal" where
"s_state_p \<equiv> (''state'', vhdl_natural, register, (exp_con (vhdl_natural, (val_i 0))))"

definition s_reg1_p:: "signal" where
"s_reg1_p \<equiv> (''reg1'', vhdl_natural, register, (exp_con (vhdl_natural, (val_i 0))))"

definition s_reg2_p:: "signal" where
"s_reg2_p \<equiv> (''reg2'', vhdl_natural, register, (exp_con (vhdl_natural, (val_i 0))))"

definition s_result_p:: "signal" where
"s_result_p \<equiv> (''result'', vhdl_natural, register, (exp_con (vhdl_natural, (val_i 0))))"

definition s_count_p:: "signal" where
"s_count_p \<equiv> (''count'', vhdl_natural, register, (exp_con (vhdl_natural, (val_i 0))))"

definition s_req_p:: "signal" where
"s_req_p \<equiv> (''req'', vhdl_bit, register, (exp_con (vhdl_natural, (val_c (CHR ''0'')))))"

definition s_ack_p:: "signal" where
"s_ack_p \<equiv> (''ack'', vhdl_bit, register, (exp_con (vhdl_natural, (val_c (CHR ''0'')))))"

definition vhdl_power:: "vhdl_desc_complex" where
"vhdl_power \<equiv>
  let env = \<lparr>env_sp = [sp_p p_clk, sp_p p_arg1_p, sp_p p_arg2_p, sp_p p_start_p, sp_p p_res_p, sp_p p_done_p,
                       sp_s s_state_p, sp_s s_reg1_p, sp_s s_reg2_p, sp_s s_result_p, sp_s s_count_p,
                       sp_s s_req_p, sp_s s_ack_p
              ],
             env_v = [],
             env_t = []\<rparr>;
      resfn = \<lambda>x.(None);
      cst_list = [
        (''MULTIPLIER'': PROCESS ([sp_p p_clk])
          BEGIN [
            ('''': IF (bexpr (exp_sig s_req_p) [=] (exp_con (vhdl_bit, (val_c (CHR ''1'')))))
              THEN [
                ('''': (clhs_sp (lhs_s (sp_s s_result_p))) <= (rhs_e (bexpa (exp_sig s_reg1_p) [*] (exp_sig s_reg2_p))))
              ]
              [] ELSE [] END IF
            ),
            ('''': (clhs_sp (lhs_s (sp_s s_ack_p))) <= (rhs_e (exp_sig s_req_p)))
          ]
          END PROCESS
        ),
        (''CONTROLLER'': PROCESS ([sp_p p_clk])
          BEGIN [
            ('''': IF (bexpr (exp_sig s_state_p) [=] (exp_con (vhdl_natural, (val_i 0))))
              THEN [
                ('''': IF (bexpr (exp_prt p_start_p) [=] (exp_con (vhdl_bit, (val_c (CHR ''1'')))))
                  THEN [
                    ('''': (clhs_sp (lhs_s (sp_s s_reg1_p))) <= (rhs_e (exp_prt p_arg1_p))),
                    ('''': (clhs_sp (lhs_s (sp_s s_reg2_p))) <= (rhs_e (exp_con (vhdl_natural, (val_i 1))))),
                    ('''': (clhs_sp (lhs_s (sp_s s_count_p))) <= (rhs_e (exp_prt p_arg2_p))),
                    ('''': (clhs_sp (lhs_s (sp_s s_state_p))) <= (rhs_e (exp_con (vhdl_natural, (val_i 1)))))
                  ]
                  [] ELSE [] END IF
                )
              ]
              [] ELSE [
                ('''': IF (bexpr (exp_sig s_state_p) [=] (exp_con (vhdl_natural, (val_i 1))))
                  THEN [
                    ('''': IF (bexpr (exp_sig s_count_p) [=] (exp_con (vhdl_natural, (val_i 0))))
                      THEN [
                        ('''': (clhs_sp (lhs_s (sp_p p_res_p))) <= (rhs_e (exp_sig s_reg2_p))),
                        ('''': (clhs_sp (lhs_s (sp_p p_done_p))) <= (rhs_e (exp_con (vhdl_bit, (val_c (CHR ''1'')))))),
                        ('''': (clhs_sp (lhs_s (sp_s s_state_p))) <= (rhs_e (exp_con (vhdl_natural, (val_i 4)))))
                      ]
                      [] ELSE [
                        ('''': (clhs_sp (lhs_s (sp_s s_req_p))) <= (rhs_e (exp_con (vhdl_bit, (val_c (CHR ''1'')))))),
                        ('''': (clhs_sp (lhs_s (sp_s s_state_p))) <= (rhs_e (exp_con (vhdl_natural, (val_i 2)))))
                      ] 
                      END IF
                    )
                  ]
                  [] ELSE [
                    ('''': IF (bexpr (exp_sig s_state_p) [=] (exp_con (vhdl_natural, (val_i 2))))
                      THEN [
                        ('''': IF (bexpr (exp_sig s_ack_p) [=] (exp_con (vhdl_bit, (val_c (CHR ''1'')))))
                          THEN [
                            ('''': (clhs_sp (lhs_s (sp_s s_reg2_p))) <= (rhs_e (exp_sig s_result_p))),
                            ('''': (clhs_sp (lhs_s (sp_s s_req_p))) <= (rhs_e (exp_con (vhdl_bit, (val_c (CHR ''0'')))))),
                            ('''': (clhs_sp (lhs_s (sp_s s_state_p))) <= (rhs_e (exp_con (vhdl_natural, (val_i 3)))))
                          ]
                          [] ELSE [] END IF
                        )
                      ]
                      [] ELSE [
                        ('''': IF (bexpr (exp_sig s_state_p) [=] (exp_con (vhdl_natural, (val_i 3))))
                          THEN [
                            ('''': (clhs_sp (lhs_s (sp_s s_count_p))) <= (rhs_e (bexpa (exp_sig s_count_p) [-] (exp_con (vhdl_natural, (val_i 1)))))),
                            ('''': (clhs_sp (lhs_s (sp_s s_state_p))) <= (rhs_e (exp_con (vhdl_natural, (val_i 1)))))
                          ]
                          [] ELSE [
                            ('''': IF (bexpr (exp_sig s_state_p) [=] (exp_con (vhdl_natural, (val_i 4))))
                              THEN [
                                ('''': IF (bexpr (exp_prt p_start_p) [=] (exp_con (vhdl_bit, (val_c (CHR ''0'')))))
                                  THEN [
                                    ('''': (clhs_sp (lhs_s (sp_p p_done_p))) <= (rhs_e (exp_con (vhdl_bit, (val_c (CHR ''0'')))))),
                                    ('''': (clhs_sp (lhs_s (sp_s s_state_p))) <= (rhs_e (exp_con (vhdl_natural, (val_i 1)))))
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

export_code vhdl_power simulation init_state trans_vhdl_desc_complex in OCaml
module_name vhdl_power file vhdl_power

end