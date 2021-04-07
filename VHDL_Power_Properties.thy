(*
 * Copyright 2016, NTU
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * Author: Zhe Hou.
 *)

theory VHDL_Power_Properties
imports Main VHDL_Hoare VHDL_Power VHDL_Power_Comp
begin

definition f:: "nat \<Rightarrow> nat" where "f x = x + 1"

definition val_op_power:: "val option \<Rightarrow> val option \<Rightarrow> val option" where
"val_op_power vop1 vop2 \<equiv> 
  case (vop1,vop2) of (Some (val_i v1), Some (val_i v2)) \<Rightarrow> Some (val_i (v1 ^ (nat v2)))
  | _ \<Rightarrow> None
"

definition input_state_p:: "int \<Rightarrow> int \<Rightarrow> vhdl_state" where
"input_state_p i j \<equiv> init_state\<lparr>state_sp := 
(state_sp init_state)((sp_p p_arg1_p) := (Some (val_i i)), 
                      (sp_p p_arg2_p) := (Some (val_i j)))\<rparr>"

definition input_state_pc:: "int \<Rightarrow> int \<Rightarrow> vhdl_arch_state" where
"input_state_pc i j \<equiv> arch_state (''POWER'',init_state\<lparr>state_sp := 
(state_sp init_state)((sp_p p_arg1_pc) := (Some (val_i i)), 
                      (sp_p p_arg2_pc) := (Some (val_i j)))\<rparr>,
  [(mult_unit_comp_map,init_arch_state_mult)])"

definition final_state where "final_state \<equiv> 
simulation 15 (trans_vhdl_desc_complex vhdl_power) (input_state_p 4 2)"

definition final_state_n where "final_state_n n x y \<equiv> 
simulation n (trans_vhdl_desc_complex vhdl_power) (input_state_p x y)"

definition vhdl_power_core:: "vhdl_desc" where
"vhdl_power_core \<equiv> trans_vhdl_desc_complex vhdl_power"

definition mult_proc:: "conc_stmt" where
"mult_proc \<equiv> cst_ps ''MULTIPLIER'' [sp_p p_clk]
  [(sst_if '''' (bexpr (exp_sig s_req_p) [=] (exp_con (vhdl_bit, (val_c (CHR ''1'')))))
    [(sst_sa '''' (clhs_sp (lhs_s (sp_s s_result_p))) 
      (rhs_e (bexpa (exp_sig s_reg1_p) [*] (exp_sig s_reg2_p))))
    ] []),
   (sst_sa '''' (clhs_sp (lhs_s (sp_s s_ack_p))) (rhs_e (exp_sig s_req_p)))
  ]
"

definition ctrl_proc:: "conc_stmt" where
"ctrl_proc \<equiv> cst_ps ''CONTROLLER'' [sp_p p_clk] 
  [(sst_if '''' (bexpr (exp_sig s_state_p) [=] (exp_con (vhdl_natural, (val_i 0))))
    [(sst_if '''' (bexpr (exp_prt p_start_p) [=] (exp_con (vhdl_bit, (val_c (CHR ''1'')))))
      [(sst_sa '''' (clhs_sp (lhs_s (sp_s s_reg1_p))) (rhs_e (exp_prt p_arg1_p))),
       (sst_sa '''' (clhs_sp (lhs_s (sp_s s_reg2_p))) (rhs_e (exp_con (vhdl_natural, (val_i 1))))),
       (sst_sa '''' (clhs_sp (lhs_s (sp_s s_count_p))) (rhs_e (exp_prt p_arg2_p))),
       (sst_sa '''' (clhs_sp (lhs_s (sp_s s_state_p))) (rhs_e (exp_con (vhdl_natural, (val_i 1)))))
      ] [])
    ] [
     (sst_if '''' (bexpr (exp_sig s_state_p) [=] (exp_con (vhdl_natural, (val_i 1))))
      [(sst_if '''' (bexpr (exp_sig s_count_p) [=] (exp_con (vhdl_natural, (val_i 0))))
        [(sst_sa '''' (clhs_sp (lhs_s (sp_p p_res_p))) (rhs_e (exp_sig s_reg2_p))),
         (sst_sa '''' (clhs_sp (lhs_s (sp_p p_done_p))) (rhs_e (exp_con (vhdl_bit, (val_c (CHR ''1'')))))),
         (sst_sa '''' (clhs_sp (lhs_s (sp_s s_state_p))) (rhs_e (exp_con (vhdl_natural, (val_i 4)))))
        ] [
         (sst_sa '''' (clhs_sp (lhs_s (sp_s s_req_p))) (rhs_e (exp_con (vhdl_bit, (val_c (CHR ''1'')))))),
         (sst_sa '''' (clhs_sp (lhs_s (sp_s s_state_p))) (rhs_e (exp_con (vhdl_natural, (val_i 2)))))
        ])
      ] [
       (sst_if '''' (bexpr (exp_sig s_state_p) [=] (exp_con (vhdl_natural, (val_i 2))))
        [(sst_if '''' (bexpr (exp_sig s_ack_p) [=] (exp_con (vhdl_bit, (val_c (CHR ''1'')))))
          [(sst_sa '''' (clhs_sp (lhs_s (sp_s s_reg2_p))) (rhs_e (exp_sig s_result_p))),
           (sst_sa '''' (clhs_sp (lhs_s (sp_s s_req_p))) (rhs_e (exp_con (vhdl_bit, (val_c (CHR ''0'')))))),
           (sst_sa '''' (clhs_sp (lhs_s (sp_s s_state_p))) (rhs_e (exp_con (vhdl_natural, (val_i 3)))))
          ] [])
        ] [
         (sst_if '''' (bexpr (exp_sig s_state_p) [=] (exp_con (vhdl_natural, (val_i 3))))
          [(sst_sa '''' (clhs_sp (lhs_s (sp_s s_count_p))) (rhs_e (bexpa (exp_sig s_count_p) [-] (exp_con (vhdl_natural, (val_i 1)))))),
           (sst_sa '''' (clhs_sp (lhs_s (sp_s s_state_p))) (rhs_e (exp_con (vhdl_natural, (val_i 1)))))
          ] [
           (sst_if '''' (bexpr (exp_sig s_state_p) [=] (exp_con (vhdl_natural, (val_i 4))))
            [(sst_if '''' (bexpr (exp_prt p_start_p) [=] (exp_con (vhdl_bit, (val_c (CHR ''0'')))))
              [(sst_sa '''' (clhs_sp (lhs_s (sp_p p_done_p))) (rhs_e (exp_con (vhdl_bit, (val_c (CHR ''0'')))))),
               (sst_sa '''' (clhs_sp (lhs_s (sp_s s_state_p))) (rhs_e (exp_con (vhdl_natural, (val_i 1)))))
              ] [])
            ] [])
          ])
        ])
      ])
    ])
  ]
"

text {* Functional correctness of the MULTIPLIER process. *}

lemma fun_cor_mult_sub3: "valid_hoare_tuple (multi_proc, [], 
((\<lambda>y. (\<lambda>x. (state_sp x) (sp_s s_req_p) = Some (val_c (CHR ''1'')) \<and>
     (((state_sp x) (sp_s s_reg1_p) = Some (val_i v1) \<and>
     (state_sp x) (sp_s s_reg2_p) = Some (val_i v2)) \<longrightarrow>
     (\<exists>r. ((state_dr_val x) (sp_s s_result_p) multi_proc = Some (val_i r) \<and>  
     r = v1 * v2))))
   (y\<lparr>state_dr_val := (state_dr_val y)
   ((sp_s s_result_p) := ((state_dr_val y) (sp_s s_result_p))
   (multi_proc := state_val_exp_t 
   (bexpa (exp_sig s_reg1_p) [*] (exp_sig s_reg2_p)) y))\<rparr>))
  \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x)))),
[(sst_sa '''' (clhs_sp (lhs_s (sp_s s_result_p))) 
      (rhs_e (bexpa (exp_sig s_reg1_p) [*] (exp_sig s_reg2_p))))],
((\<lambda>x. (state_sp x) (sp_s s_req_p) = Some (val_c (CHR ''1'')) \<and>
     (((state_sp x) (sp_s s_reg1_p) = Some (val_i v1) \<and>
     (state_sp x) (sp_s s_reg2_p) = Some (val_i v2)) \<longrightarrow>
     (\<exists>r. ((state_dr_val x) (sp_s s_result_p) multi_proc = Some (val_i r) \<and>  
     r = v1 * v2))))
  \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x))))
)
"
using VHDL_Hoare.sig_asmt by meson

lemma "\<forall>w. (\<lambda>x. (state_sp x) (sp_s s_req_p) = Some (val_c (CHR ''1'')) \<and>
     (((state_sp x) (sp_s s_reg1_p) = Some (val_i v1) \<and>
     (state_sp x) (sp_s s_reg2_p) = Some (val_i v2)) \<longrightarrow>
     (\<exists>r. (state_val_exp_t (bexpa (exp_sig s_reg1_p) [*] (exp_sig s_reg2_p)) x = Some (val_i r) \<and>  
     r = v1 * v2)))) w \<longrightarrow>
(\<lambda>y. (\<lambda>x. (state_sp x) (sp_s s_req_p) = Some (val_c (CHR ''1'')) \<and>
     (((state_sp x) (sp_s s_reg1_p) = Some (val_i v1) \<and>
     (state_sp x) (sp_s s_reg2_p) = Some (val_i v2)) \<longrightarrow>
     (\<exists>r. ((state_dr_val x) (sp_s s_result_p) multi_proc = Some (val_i r) \<and>  
     r = v1 * v2))))
   (y\<lparr>state_dr_val := (state_dr_val y)
   ((sp_s s_result_p) := ((state_dr_val y) (sp_s s_result_p))
   (multi_proc := state_val_exp_t 
   (bexpa (exp_sig s_reg1_p) [*] (exp_sig s_reg2_p)) y))\<rparr>)) w"
by auto

lemma "\<forall>w. (\<lambda>x. (state_sp x) (sp_s s_req_p) = Some (val_c (CHR ''1'')) \<and>
     (state_sp x) (sp_s s_reg1_p) = Some (val_i v1) \<and>
     (state_sp x) (sp_s s_reg2_p) = Some (val_i v2)) w \<longrightarrow>
     (\<lambda>x. (state_sp x) (sp_s s_req_p) = Some (val_c (CHR ''1'')) \<and>
     (((state_sp x) (sp_s s_reg1_p) = Some (val_i v1) \<and>
     (state_sp x) (sp_s s_reg2_p) = Some (val_i v2)) \<longrightarrow>
     (\<exists>r. (state_val_exp_t (bexpa (exp_sig s_reg1_p) [*] (exp_sig s_reg2_p)) x = Some (val_i r) \<and>  
     r = v1 * v2)))) w" 
apply clarsimp
apply (simp add: state_val_exp_t_def s_reg1_p_def s_reg2_p_def)
apply (simp add: val_arith_def)
by (simp add: vhdl_natural_def vhdl_positive_def vhdl_real_def)

lemma fun_cor_mult_sub3_1: "valid_hoare_tuple (multi_proc, [], 
((\<lambda>x. (state_sp x) (sp_s s_req_p) = Some (val_c (CHR ''1'')) \<and>
     (state_sp x) (sp_s s_reg1_p) = Some (val_i v1) \<and>
     (state_sp x) (sp_s s_reg2_p) = Some (val_i v2))
  \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x))) 
  \<sqinter> (\<lambda>x. (state_val_exp_t (bexpr (exp_sig s_req_p) [=] 
    (exp_con (vhdl_bit, (val_c (CHR ''1''))))) x = Some (val_b True)))),
[(sst_sa '''' (clhs_sp (lhs_s (sp_s s_result_p))) 
      (rhs_e (bexpa (exp_sig s_reg1_p) [*] (exp_sig s_reg2_p))))],
((\<lambda>x. (state_sp x) (sp_s s_req_p) = Some (val_c (CHR ''1'')) \<and>
     (((state_sp x) (sp_s s_reg1_p) = Some (val_i v1) \<and>
     (state_sp x) (sp_s s_reg2_p) = Some (val_i v2)) \<longrightarrow>
     (\<exists>r. ((state_dr_val x) (sp_s s_result_p) multi_proc = Some (val_i r) \<and>  
     r = v1 * v2))))
  \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x))))
)
"
proof -
def "P" \<equiv> "((\<lambda>y. (\<lambda>x. (state_sp x) (sp_s s_req_p) = Some (val_c (CHR ''1'')) \<and>
     (((state_sp x) (sp_s s_reg1_p) = Some (val_i v1) \<and>
     (state_sp x) (sp_s s_reg2_p) = Some (val_i v2)) \<longrightarrow>
     (\<exists>r. ((state_dr_val x) (sp_s s_result_p) multi_proc = Some (val_i r) \<and>  
     r = v1 * v2))))
   (y\<lparr>state_dr_val := (state_dr_val y)
   ((sp_s s_result_p) := ((state_dr_val y) (sp_s s_result_p))
   (multi_proc := state_val_exp_t 
   (bexpa (exp_sig s_reg1_p) [*] (exp_sig s_reg2_p)) y))\<rparr>))
  \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x))))"
def "C" \<equiv> "[(sst_sa '''' (clhs_sp (lhs_s (sp_s s_result_p))) 
      (rhs_e (bexpa (exp_sig s_reg1_p) [*] (exp_sig s_reg2_p))))]"
def "Q" \<equiv> "((\<lambda>x. (state_sp x) (sp_s s_req_p) = Some (val_c (CHR ''1'')) \<and>
     (((state_sp x) (sp_s s_reg1_p) = Some (val_i v1) \<and>
     (state_sp x) (sp_s s_reg2_p) = Some (val_i v2)) \<longrightarrow>
     (\<exists>r. ((state_dr_val x) (sp_s s_result_p) multi_proc = Some (val_i r) \<and>  
     r = v1 * v2))))
  \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x))))"
def "P'" \<equiv> "(\<lambda>x. (state_sp x) (sp_s s_req_p) = Some (val_c (CHR ''1'')) \<and>
     (((state_sp x) (sp_s s_reg1_p) = Some (val_i v1) \<and>
     (state_sp x) (sp_s s_reg2_p) = Some (val_i v2)) \<longrightarrow>
     (\<exists>r. (state_val_exp_t (bexpa (exp_sig s_reg1_p) [*] (exp_sig s_reg2_p)) x = Some (val_i r) \<and>  
     r = v1 * v2)))) \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x)))"
def "P''" \<equiv> "(\<lambda>x. (state_sp x) (sp_s s_req_p) = Some (val_c (CHR ''1'')) \<and>
     (state_sp x) (sp_s s_reg1_p) = Some (val_i v1) \<and>
     (state_sp x) (sp_s s_reg2_p) = Some (val_i v2)) 
     \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x)))"
def "P'''" \<equiv> "((\<lambda>x. (state_sp x) (sp_s s_req_p) = Some (val_c (CHR ''1'')) \<and>
     (state_sp x) (sp_s s_reg1_p) = Some (val_i v1) \<and>
     (state_sp x) (sp_s s_reg2_p) = Some (val_i v2))
  \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x))) 
  \<sqinter> (\<lambda>x. (state_val_exp_t (bexpr (exp_sig s_req_p) [=] 
    (exp_con (vhdl_bit, (val_c (CHR ''1''))))) x = Some (val_b True))))"
  have f0: "valid_hoare_tuple (multi_proc, [], P, C, Q)" 
    using fun_cor_mult_sub3 unfolding P_def C_def Q_def by auto
  have f1: "\<forall>w. P' w \<longrightarrow> P w" unfolding P'_def P_def asst_and_def 
    by auto
  have f2: "\<forall>w. P'' w \<longrightarrow> P' w" unfolding P''_def P'_def asst_and_def
    apply clarsimp
    apply (simp add: state_val_exp_t_def s_reg1_p_def s_reg2_p_def)
    apply (simp add: val_arith_def)
    by (simp add: vhdl_natural_def vhdl_positive_def vhdl_real_def)
  have f3: "\<forall>w. P''' w \<longrightarrow> P'' w" unfolding P'''_def P''_def asst_and_def
    by auto
  from f1 f2 f3 have f4: "\<forall>w. P''' w \<longrightarrow> P w" by auto
  have f5: "\<forall>w. Q w \<longrightarrow> Q w" by auto
  from f0 f4 f5 have "valid_hoare_tuple (multi_proc, [], P''', C, Q)"
    using consequence by auto  
  then show ?thesis using P'''_def C_def Q_def by auto
qed

lemma fun_cor_mult_sub4: "valid_hoare_tuple (multi_proc, [], 
((\<lambda>x. (state_sp x) (sp_s s_req_p) = Some (val_c (CHR ''1'')) \<and>
     (state_sp x) (sp_s s_reg1_p) = Some (val_i v1) \<and>
     (state_sp x) (sp_s s_reg2_p) = Some (val_i v2))
  \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x))) 
  \<sqinter> (\<lambda>x. (state_val_exp_t (bexpr (exp_sig s_req_p) [=] 
    (exp_con (vhdl_bit, (val_c (CHR ''1''))))) x \<noteq> Some (val_b True)))),
[],
((\<lambda>x. (state_sp x) (sp_s s_req_p) = Some (val_c (CHR ''1'')) \<and>
     (((state_sp x) (sp_s s_reg1_p) = Some (val_i v1) \<and>
     (state_sp x) (sp_s s_reg2_p) = Some (val_i v2)) \<longrightarrow>
     (\<exists>r. ((state_dr_val x) (sp_s s_result_p) multi_proc = Some (val_i r) \<and>  
     r = v1 * v2))))
  \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x))))
)
"
proof -
def "Q" \<equiv> "((\<lambda>x. (state_sp x) (sp_s s_req_p) = Some (val_c (CHR ''1'')) \<and>
     (((state_sp x) (sp_s s_reg1_p) = Some (val_i v1) \<and>
     (state_sp x) (sp_s s_reg2_p) = Some (val_i v2)) \<longrightarrow>
     (\<exists>r. ((state_dr_val x) (sp_s s_result_p) multi_proc = Some (val_i r) \<and>  
     r = v1 * v2))))
  \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x))))"
def "P" \<equiv> "((\<lambda>x. (state_sp x) (sp_s s_req_p) = Some (val_c (CHR ''1'')) \<and>
     (state_sp x) (sp_s s_reg1_p) = Some (val_i v1) \<and>
     (state_sp x) (sp_s s_reg2_p) = Some (val_i v2))
  \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x))) 
  \<sqinter> (\<lambda>x. (state_val_exp_t (bexpr (exp_sig s_req_p) [=] 
    (exp_con (vhdl_bit, (val_c (CHR ''1''))))) x \<noteq> Some (val_b True))))"
  have f1: "valid_hoare_tuple (multi_proc, [], Q, [], Q)" using skip by auto
  have f2: "\<forall>w. P w \<longrightarrow> Q w" unfolding P_def Q_def asst_and_def
    apply auto
    apply (simp add: state_val_exp_t_def s_req_p_def)
    apply (simp add: val_rel_def)
    by (simp add: vhdl_bit_def vhdl_boolean_def)
  then have "valid_hoare_tuple (multi_proc, [], P, [], Q)" using f1 consequence
    by auto
  then show ?thesis unfolding P_def Q_def
    by auto
qed

lemma fun_cor_mult_sub2: "valid_hoare_tuple (multi_proc, [], 
(\<lambda>x. (state_sp x) (sp_s s_req_p) = Some (val_c (CHR ''1'')) \<and>
     (state_sp x) (sp_s s_reg1_p) = Some (val_i v1) \<and>
     (state_sp x) (sp_s s_reg2_p) = Some (val_i v2))
  \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x))),
[(sst_if '''' (bexpr (exp_sig s_req_p) [=] (exp_con (vhdl_bit, (val_c (CHR ''1'')))))
    [(sst_sa '''' (clhs_sp (lhs_s (sp_s s_result_p))) 
      (rhs_e (bexpa (exp_sig s_reg1_p) [*] (exp_sig s_reg2_p))))
    ] [])],
((\<lambda>x. (state_sp x) (sp_s s_req_p) = Some (val_c (CHR ''1'')) \<and>
     ((state_sp x) (sp_s s_reg1_p) = Some (val_i v1) \<and>
     ((state_sp x) (sp_s s_reg2_p) = Some (val_i v2)) \<longrightarrow>
     (\<exists>r. ((state_dr_val x) (sp_s s_result_p) multi_proc = Some (val_i r) \<and>  
     r = v1 * v2))))
  \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x))))
)
"
using fun_cor_mult_sub3_1 fun_cor_mult_sub4 if_stmt
by auto

lemma fun_cor_mult_sub1: "valid_hoare_tuple (multi_proc, [], 
((\<lambda>y. (\<lambda>x. (state_dr_val x) (sp_s s_ack_p) multi_proc = Some (val_c (CHR ''1'')) \<and>
     (((state_sp x) (sp_s s_reg1_p) = Some (val_i v1) \<and>
     (state_sp x) (sp_s s_reg2_p) = Some (val_i v2)) \<longrightarrow>
     (\<exists>r. ((state_dr_val x) (sp_s s_result_p) multi_proc = Some (val_i r) \<and>  
     r = v1 * v2))))
   (y\<lparr>state_dr_val := (state_dr_val y)
   ((sp_s s_ack_p) := ((state_dr_val y) (sp_s s_ack_p))
   (multi_proc := state_val_exp_t (exp_sig s_req_p) y))\<rparr>))
  \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x)))),
[(sst_sa '''' (clhs_sp (lhs_s (sp_s s_ack_p))) (rhs_e (exp_sig s_req_p)))],
((\<lambda>x. (state_dr_val x) (sp_s s_ack_p) multi_proc = Some (val_c (CHR ''1'')) \<and>
     (((state_sp x) (sp_s s_reg1_p) = Some (val_i v1) \<and>
     (state_sp x) (sp_s s_reg2_p) = Some (val_i v2)) \<longrightarrow>
     (\<exists>r. ((state_dr_val x) (sp_s s_result_p) multi_proc = Some (val_i r) \<and>  
     r = v1 * v2))))
  \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x))))
)
"
using VHDL_Hoare.sig_asmt by meson

lemma fun_cor_mult_sub1_1: "valid_hoare_tuple (multi_proc, [], 
((\<lambda>x. (state_sp x) (sp_s s_req_p) = Some (val_c (CHR ''1'')) \<and>
     (((state_sp x) (sp_s s_reg1_p) = Some (val_i v1) \<and>
     (state_sp x) (sp_s s_reg2_p) = Some (val_i v2)) \<longrightarrow>
     (\<exists>r. ((state_dr_val x) (sp_s s_result_p) multi_proc = Some (val_i r) \<and>  
     r = v1 * v2))))
  \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x)))),
[(sst_sa '''' (clhs_sp (lhs_s (sp_s s_ack_p))) (rhs_e (exp_sig s_req_p)))],
((\<lambda>x. (state_dr_val x) (sp_s s_ack_p) multi_proc = Some (val_c (CHR ''1'')) \<and>
     (((state_sp x) (sp_s s_reg1_p) = Some (val_i v1) \<and>
     (state_sp x) (sp_s s_reg2_p) = Some (val_i v2)) \<longrightarrow>
     (\<exists>r. ((state_dr_val x) (sp_s s_result_p) multi_proc = Some (val_i r) \<and>  
     r = v1 * v2))))
  \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x))))
)
"
proof -
def "P" \<equiv> "((\<lambda>y. (\<lambda>x. (state_dr_val x) (sp_s s_ack_p) multi_proc = Some (val_c (CHR ''1'')) \<and>
     ((state_sp x) (sp_s s_reg1_p) = Some (val_i v1) \<and>
     ((state_sp x) (sp_s s_reg2_p) = Some (val_i v2)) \<longrightarrow>
     (\<exists>r. ((state_dr_val x) (sp_s s_result_p) multi_proc = Some (val_i r) \<and>  
     r = v1 * v2))))
   (y\<lparr>state_dr_val := (state_dr_val y)
   ((sp_s s_ack_p) := ((state_dr_val y) (sp_s s_ack_p))
   (multi_proc := state_val_exp_t (exp_sig s_req_p) y))\<rparr>))
  \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x))))"
def "C" \<equiv> "[(sst_sa '''' (clhs_sp (lhs_s (sp_s s_ack_p))) (rhs_e (exp_sig s_req_p)))]"
def "Q" \<equiv> "((\<lambda>x. (state_dr_val x) (sp_s s_ack_p) multi_proc = Some (val_c (CHR ''1'')) \<and>
     ((state_sp x) (sp_s s_reg1_p) = Some (val_i v1) \<and>
     ((state_sp x) (sp_s s_reg2_p) = Some (val_i v2)) \<longrightarrow>
     (\<exists>r. ((state_dr_val x) (sp_s s_result_p) multi_proc = Some (val_i r) \<and>  
     r = v1 * v2))))
  \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x))))"
def "P'" \<equiv> "((\<lambda>x. (state_sp x) (sp_s s_req_p) = Some (val_c (CHR ''1'')) \<and>
     ((state_sp x) (sp_s s_reg1_p) = Some (val_i v1) \<and>
     ((state_sp x) (sp_s s_reg2_p) = Some (val_i v2)) \<longrightarrow>
     (\<exists>r. ((state_dr_val x) (sp_s s_result_p) multi_proc = Some (val_i r) \<and>  
     r = v1 * v2))))
  \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x))))"
  have f1: "valid_hoare_tuple (multi_proc, [], P, C, Q)"
    unfolding P_def C_def Q_def using fun_cor_mult_sub1 by auto
  have f2: "\<forall>x. P' x \<longrightarrow> P x" unfolding P'_def P_def
    unfolding asst_and_def
    apply auto
      unfolding state_val_exp_t_def
      apply (cases "exp_type (exp_sig s_req_p) = None")
       apply auto
    unfolding s_result_p_def s_ack_p_def
    by auto
  have f3: "\<forall>x. Q x \<longrightarrow> Q x" by auto
  then have "valid_hoare_tuple (multi_proc, [], P', C, Q)"
    using consequence f1 f2 f3 by auto
  then show ?thesis unfolding P'_def C_def Q_def
    by auto
qed

lemma fun_cor_mult: "valid_hoare_tuple (multi_proc, [], 
(\<lambda>x. (state_sp x) (sp_s s_req_p) = Some (val_c (CHR ''1'')) \<and>
     (state_sp x) (sp_s s_reg1_p) = Some (val_i v1) \<and>
     (state_sp x) (sp_s s_reg2_p) = Some (val_i v2))
  \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x))), 
[(sst_if '''' (bexpr (exp_sig s_req_p) [=] (exp_con (vhdl_bit, (val_c (CHR ''1'')))))
    [(sst_sa '''' (clhs_sp (lhs_s (sp_s s_result_p))) 
      (rhs_e (bexpa (exp_sig s_reg1_p) [*] (exp_sig s_reg2_p))))
    ] []),
   (sst_sa '''' (clhs_sp (lhs_s (sp_s s_ack_p))) (rhs_e (exp_sig s_req_p)))
], 
((\<lambda>x. (state_dr_val x) (sp_s s_ack_p) multi_proc = Some (val_c (CHR ''1'')) \<and>
     (((state_sp x) (sp_s s_reg1_p) = Some (val_i v1) \<and>
     (state_sp x) (sp_s s_reg2_p) = Some (val_i v2)) \<longrightarrow>
     (\<exists>r. ((state_dr_val x) (sp_s s_result_p) multi_proc = Some (val_i r) \<and>  
     r = v1 * v2))))
  \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x))))
)"
proof -
def "P" \<equiv> "(\<lambda>x. (state_sp x) (sp_s s_req_p) = Some (val_c (CHR ''1'')) \<and>
     (state_sp x) (sp_s s_reg1_p) = Some (val_i v1) \<and>
     (state_sp x) (sp_s s_reg2_p) = Some (val_i v2))::asst"
def "C1" \<equiv> "[(sst_if '''' (bexpr (exp_sig s_req_p) [=] (exp_con (vhdl_bit, (val_c (CHR ''1'')))))
    [(sst_sa '''' (clhs_sp (lhs_s (sp_s s_result_p))) 
      (rhs_e (bexpa (exp_sig s_reg1_p) [*] (exp_sig s_reg2_p))))
    ] [])]"
def "Q" \<equiv> "(\<lambda>x. (state_sp x) (sp_s s_req_p) = Some (val_c (CHR ''1'')) \<and>
     ((state_sp x) (sp_s s_reg1_p) = Some (val_i v1) \<and>
     ((state_sp x) (sp_s s_reg2_p) = Some (val_i v2)) \<longrightarrow>
     (\<exists>r. ((state_dr_val x) (sp_s s_result_p) multi_proc = Some (val_i r) \<and>  
     r = v1 * v2))))::asst"
def "C2" \<equiv> "[(sst_sa '''' (clhs_sp (lhs_s (sp_s s_ack_p))) (rhs_e (exp_sig s_req_p)))]"
def "R" \<equiv> "(\<lambda>x. (state_dr_val x) (sp_s s_ack_p) multi_proc = Some (val_c (CHR ''1'')) \<and>
     (((state_sp x) (sp_s s_reg1_p) = Some (val_i v1) \<and>
     (state_sp x) (sp_s s_reg2_p) = Some (val_i v2)) \<longrightarrow>
     (\<exists>r. ((state_dr_val x) (sp_s s_result_p) multi_proc = Some (val_i r) \<and>  
     r = v1 * v2))))::asst"
  from fun_cor_mult_sub2 have f1: "valid_hoare_tuple (multi_proc, [], 
    (P \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x)))), C1, 
    (Q \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x)))))" 
    unfolding P_def C1_def Q_def by auto
  from fun_cor_mult_sub1_1 have f2: "valid_hoare_tuple (multi_proc, [], 
    (Q \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x)))), C2, 
    (R \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x)))))"
    unfolding Q_def C2_def R_def by auto
  from f1 f2 if_stmt_seq have "valid_hoare_tuple (multi_proc, [], 
    (P \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x)))), C1@C2, 
    (R \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x)))))"
    unfolding C1_def by auto
  then show ?thesis unfolding P_def R_def C1_def C2_def by auto
qed


theorem power_correct: "\<exists>(m::nat). (\<forall>(n::nat). 
(((n \<ge> m)) \<longrightarrow> 
(((state_sp (simulation n (trans_vhdl_desc_complex vhdl_power) init_state)) (sp_p p_res_p)) = 
val_op_power ((state_sp init_state) (sp_p p_arg1_p)) ((state_sp init_state) (sp_p p_arg2_p)))))"

sorry

theorem power_comp_correct: "\<exists>(m::nat). (\<forall>(n::nat). 
(((n \<ge> m)) \<longrightarrow> 
(((state_sp (state_of_arch (sim_arch n vhdl_power_comp init_arch_state_power))) (sp_p p_res_pc)) = 
val_op_power ((state_sp (state_of_arch init_arch_state_power)) (sp_p p_arg1_pc)) 
  ((state_sp (state_of_arch init_arch_state_power)) (sp_p p_arg2_pc)))))"
sorry

theorem power_eq: "\<exists>(m::nat). (\<forall>(n::nat). 
(((((state_sp init_state) (sp_p p_arg1_p)) = 
((state_sp (state_of_arch init_arch_state_power)) (sp_p p_arg1_pc)) \<and> 
((state_sp init_state) (sp_p p_arg2_p)) = 
((state_sp (state_of_arch init_arch_state_power)) (sp_p p_arg2_pc))) \<and> 
(n \<ge> m)) \<longrightarrow> 
(((state_sp (simulation n (trans_vhdl_desc_complex vhdl_power) init_state)) (sp_p p_res_p)) = 
((state_sp (state_of_arch (sim_arch n vhdl_power_comp init_arch_state_power))) (sp_p p_res_pc)))))"
by (metis add_leE power_comp_correct power_correct)

end