(*
 * Copyright 2016, NTU
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * Author: Zhe Hou.
 *)

theory VHDL_Hoare
imports Main VHDL_Component VHDL_Syntax_Complex
begin

text {* Definition of an assertion about the state. *}

type_synonym asst = "vhdl_state \<Rightarrow> bool"

text {* Logical operations on assertions. *}

definition asst_not:: "asst \<Rightarrow> asst" (infixl "\<sim>" 60) where
"asst_not a1 \<equiv> \<lambda>x. \<not> (a1 x)"

definition asst_and:: "asst \<Rightarrow> asst \<Rightarrow> asst" (infixl "\<sqinter>" 60) where 
"asst_and a1 a2 \<equiv> \<lambda>x. (a1 x) \<and> (a2 x)"

definition asst_or:: "asst \<Rightarrow> asst \<Rightarrow> asst" (infixl "\<squnion>" 60) where
"asst_or a1 a2 \<equiv> \<lambda>x. (a1 x) \<or> (a2 x)"

definition asst_imp:: "asst \<Rightarrow> asst \<Rightarrow> asst" (infixl "\<sqsupset>" 60) where
"asst_imp a1 a2 \<equiv> \<lambda>x. (a1 x) \<longrightarrow> (a2 x)"

text {* Definition of a Hoare tuple.
In addition to the triple, we need to keep records of 
the current process (conc_stmt) and the list of subprograms. *}

type_synonym hoare_tuple = 
"(conc_stmt \<times> subprogram list \<times> asst \<times> seq_stmt list \<times> asst)"

definition proc_of_tuple:: "hoare_tuple \<Rightarrow> conc_stmt" where
"proc_of_tuple ht \<equiv> fst ht"

definition sp_of_tuple:: "hoare_tuple \<Rightarrow> subprogram list" where
"sp_of_tuple ht \<equiv> fst (snd ht)"

definition pre_of_tuple:: "hoare_tuple \<Rightarrow> asst" where
"pre_of_tuple ht \<equiv> fst (snd (snd ht))"

definition cmd_of_tuple:: "hoare_tuple \<Rightarrow> seq_stmt list" where
"cmd_of_tuple ht \<equiv> fst (snd (snd (snd ht)))"

definition post_of_tuple:: "hoare_tuple \<Rightarrow> asst" where
"post_of_tuple ht \<equiv> snd (snd (snd (snd ht)))"

text {* Define if a Hoare tuple is valid at a pre-state. *}

definition valid_hoare_tuple:: "hoare_tuple \<Rightarrow> bool" where
"valid_hoare_tuple ht \<equiv> \<forall>x y. ((((pre_of_tuple ht) x) \<and> 
  y = (fst (exec_seq_stmt_list (proc_of_tuple ht) (cmd_of_tuple ht) 
  (sp_of_tuple ht) x))) \<longrightarrow>
  ((post_of_tuple ht) y))"

text {* Hoare logic rule for skip. *}

lemma skip: "valid_hoare_tuple (p,sp,P,[],P)"
unfolding valid_hoare_tuple_def pre_of_tuple_def proc_of_tuple_def
cmd_of_tuple_def sp_of_tuple_def post_of_tuple_def
by auto

text {* Hoare logic rule for variable assignment
where the variable is not a vector nor a record.
We assume that the flags for next and exit are both false,
otherwise the statement won't be executed. 
Note that the flags are independent from the variable assignment
so we can separate this condition in pre and post condition. *}

lemma var_asmt: "valid_hoare_tuple (p,sp,
  ((\<lambda>x. Q(x\<lparr>state_var := (state_var x)(v := state_val_exp_t e x)\<rparr>))
    \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x)))),
  [sst_va n (clhs_v (lhs_v v)) (rhs_e e)],
  (Q \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x)))))"
unfolding valid_hoare_tuple_def 
apply auto
proof -
def "pre" \<equiv> "((\<lambda>x. Q(x\<lparr>state_var := (state_var x)(v := state_val_exp_t e x)\<rparr>))
              \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x))))"
def "post" \<equiv> "(Q \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x))))"
def "tuple" \<equiv> "(p, sp, pre, [sst_va n (clhs_v (lhs_v v)) (rhs_e e)], post)"
fix s::vhdl_state
assume a1: "pre_of_tuple tuple s"
from a1 show "post_of_tuple tuple (fst (exec_seq_stmt_list 
  (proc_of_tuple tuple) (cmd_of_tuple tuple) (sp_of_tuple tuple) s))" 
  proof -
    from a1 have "pre s"
      unfolding pre_of_tuple_def tuple_def by auto  
    then have f0: "(Q (s\<lparr>state_var := (state_var s)(v := state_val_exp_t e s)\<rparr>)
              \<and> (\<not> (snd (next_flag s))) \<and> (\<not>(snd (exit_flag s))))"
      unfolding pre_def asst_and_def by auto
    then have f1: "post_of_tuple tuple (s\<lparr>state_var := (state_var s)(v := state_val_exp_t e s)\<rparr>)"
      unfolding post_of_tuple_def tuple_def post_def asst_and_def by auto  
    have f2: "\<not> (snd (next_flag s)) \<and> \<not> (snd (exit_flag s))" using f0 by auto 
    have "(exec_var_asmt (sst_va n (clhs_v (lhs_v v)) (rhs_e e)) s) =
              (s\<lparr>state_var := (state_var s)(v := state_val_exp_t e s)\<rparr>)"
      unfolding exec_var_asmt_def by auto
    then have f3: "\<forall>proc sp. (fst (exec_seq_stmt_list proc [] sp (exec_var_asmt (sst_va n (clhs_v (lhs_v v)) (rhs_e e)) s))) =
              (s\<lparr>state_var := (state_var s)(v := state_val_exp_t e s)\<rparr>)"
      by auto
    have "\<forall>proc sp. (fst (exec_seq_stmt_list proc [sst_va n (clhs_v (lhs_v v)) (rhs_e e)] sp s)) =
         (fst (exec_seq_stmt_list proc [] sp (exec_var_asmt (sst_va n (clhs_v (lhs_v v)) (rhs_e e)) s)))"
      using f2 by simp 
    then have "\<forall>proc sp. (fst (exec_seq_stmt_list proc [sst_va n (clhs_v (lhs_v v)) (rhs_e e)] sp s)) =
              (s\<lparr>state_var := (state_var s)(v := state_val_exp_t e s)\<rparr>)" 
      using f3 by auto
    then have "\<forall>proc sp. (fst (exec_seq_stmt_list proc (cmd_of_tuple tuple) sp s)) =
              (s\<lparr>state_var := (state_var s)(v := state_val_exp_t e s)\<rparr>)"
      unfolding cmd_of_tuple_def tuple_def by auto
    then show ?thesis using f1 by auto
  qed
qed

text {* Sequential rule in the case of simple variable assignment. *}

lemma var_asmt_seq: 
assumes a1: "valid_hoare_tuple (p,sp,
(P \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x)))),
[sst_va n (clhs_v (lhs_v v)) (rhs_e e)],
(Q \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x)))))"
and a2: "valid_hoare_tuple (p,sp,
(Q \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x)))),
l,
(R\<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x)))))"
shows "valid_hoare_tuple (p,sp,
(P \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x)))),
(sst_va n (clhs_v (lhs_v v)) (rhs_e e))#l,
(R \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x)))))"
unfolding valid_hoare_tuple_def
apply auto 
proof -
def "c" \<equiv> "sst_va n (clhs_v (lhs_v v)) (rhs_e e)"
def "pre" \<equiv> "(P \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x))))"
def "post" \<equiv> "(R \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x))))"
def "tuple" \<equiv> "(p, sp, pre, c#l, post)"
fix s::vhdl_state
assume a3: "pre_of_tuple tuple s"
then have "(P \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x)))) s" 
  unfolding pre_of_tuple_def tuple_def pre_def post_def by auto
then show "post_of_tuple tuple (fst (exec_seq_stmt_list
            (proc_of_tuple tuple) (cmd_of_tuple tuple) (sp_of_tuple tuple) s))"
  proof -
    from a3 have f1: "P s \<and> \<not> (snd (next_flag s)) \<and> \<not> (snd (exit_flag s))"
      unfolding pre_of_tuple_def tuple_def pre_def asst_and_def
      by auto
    from a1 a3 have "(Q \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x)))) 
      (fst (exec_seq_stmt_list p [c] sp s))"
      unfolding valid_hoare_tuple_def proc_of_tuple_def cmd_of_tuple_def 
      sp_of_tuple_def tuple_def pre_of_tuple_def post_of_tuple_def 
      post_def pre_def c_def
      by auto
    then have "post (fst (exec_seq_stmt_list p l sp (fst (exec_seq_stmt_list p [c] sp s))))"
      using a2 unfolding valid_hoare_tuple_def proc_of_tuple_def cmd_of_tuple_def 
      sp_of_tuple_def tuple_def pre_of_tuple_def post_of_tuple_def post_def
      by auto
    then have "post (fst (exec_seq_stmt_list p (c#l) sp s))"
      unfolding post_def c_def using f1 
      by auto
    then show ?thesis
      unfolding proc_of_tuple_def cmd_of_tuple_def sp_of_tuple_def 
      tuple_def post_of_tuple_def pre_def post_def
      by auto
  qed
qed

text {* Hoare logic rule for signal assignment
where the signal/port is not a vector nor a record.
We assume that the flags for next and exit are both false,
otherwise the statement won't be executed. 
Note that the flags are independent from the signal assignment
so we can separate this condition in pre and post condition. 
Note also that we only update the driving value of the signal/port. *}

lemma sig_asmt: "valid_hoare_tuple (p,sp,
  ((\<lambda>x. Q(x\<lparr>state_dr_val := (state_dr_val x)
        (sg := ((state_dr_val x) sg)(p := state_val_exp_t e x))\<rparr>))
    \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x)))),
  [sst_sa n (clhs_sp (lhs_s sg)) (rhs_e e)],
  (Q \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x)))))"
unfolding valid_hoare_tuple_def 
apply auto
proof -
def "pre" \<equiv> "((\<lambda>x. Q(x\<lparr>state_dr_val := (state_dr_val x)
            (sg := ((state_dr_val x) sg)(p := state_val_exp_t e x))\<rparr>))
            \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x))))"
def "post" \<equiv> "(Q \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x))))"
def "tuple" \<equiv> "(p, sp, pre, [sst_sa n (clhs_sp (lhs_s sg)) (rhs_e e)], post)"
fix s::vhdl_state
assume a1: "pre_of_tuple tuple s"
then show "post_of_tuple tuple (fst (exec_seq_stmt_list
            (proc_of_tuple tuple) (cmd_of_tuple tuple) (sp_of_tuple tuple) s))"
  proof -
    from a1 have "pre s"
      unfolding pre_of_tuple_def tuple_def by auto
    then have f0: "(Q (s\<lparr>state_dr_val := (state_dr_val s)
            (sg := ((state_dr_val s) sg)(p := state_val_exp_t e s))\<rparr>))
            \<and> (\<not> (snd (next_flag s))) \<and> (\<not>(snd (exit_flag s)))"
      unfolding pre_def asst_and_def by auto
    then have f1: "post_of_tuple tuple (s\<lparr>state_dr_val := (state_dr_val s)
            (sg := ((state_dr_val s) sg)(p := state_val_exp_t e s))\<rparr>)"
      unfolding post_of_tuple_def tuple_def post_def asst_and_def by auto
    have f2: "\<not> (snd (next_flag s)) \<and> \<not> (snd (exit_flag s))" using f0 by auto 
    have "(exec_sig_asmt p (sst_sa n (clhs_sp (lhs_s sg)) (rhs_e e)) s) =
              (s\<lparr>state_dr_val := (state_dr_val s)
              (sg := ((state_dr_val s) sg)(p := state_val_exp_t e s))\<rparr>)"
      unfolding exec_sig_asmt_def by auto
    then have f3: "\<forall>sp. (fst (exec_seq_stmt_list p [] sp (exec_sig_asmt p (sst_sa n (clhs_sp (lhs_s sg)) (rhs_e e)) s))) =
              (s\<lparr>state_dr_val := (state_dr_val s)
              (sg := ((state_dr_val s) sg)(p := state_val_exp_t e s))\<rparr>)"
      by auto
    have "\<forall>sp. (fst (exec_seq_stmt_list p [sst_sa n (clhs_sp (lhs_s sg)) (rhs_e e)] sp s)) =
         (fst (exec_seq_stmt_list p [] sp (exec_sig_asmt p (sst_sa n (clhs_sp (lhs_s sg)) (rhs_e e)) s)))"
      using f2 by simp    
    then have "\<forall>sp. (fst (exec_seq_stmt_list p [sst_sa n (clhs_sp (lhs_s sg)) (rhs_e e)] sp s)) =
              (s\<lparr>state_dr_val := (state_dr_val s)
              (sg := ((state_dr_val s) sg)(p := state_val_exp_t e s))\<rparr>)" 
      using f3 by auto
    then have "\<forall>sp. (fst (exec_seq_stmt_list p (cmd_of_tuple tuple) sp s)) =
              (s\<lparr>state_dr_val := (state_dr_val s)
              (sg := ((state_dr_val s) sg)(p := state_val_exp_t e s))\<rparr>)"
      unfolding cmd_of_tuple_def tuple_def by auto
    then show ?thesis unfolding proc_of_tuple_def using f1 tuple_def 
      by auto
  qed
qed

text {* Sequential rule in the case of (simple) signal assignment. *}

lemma sig_asmt_seq: 
assumes a1: "valid_hoare_tuple (p,sp,
(P \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x)))),
[sst_sa n (clhs_sp (lhs_s sg)) (rhs_e e)],
(Q \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x)))))"
and a2: "valid_hoare_tuple (p,sp,
(Q \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x)))),
l,
(R\<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x)))))"
shows "valid_hoare_tuple (p,sp,
(P \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x)))),
(sst_sa n (clhs_sp (lhs_s sg)) (rhs_e e))#l,
(R \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x)))))"
unfolding valid_hoare_tuple_def
apply auto 
proof -
def "c" \<equiv> "sst_sa n (clhs_sp (lhs_s sg)) (rhs_e e)"
def "pre" \<equiv> "(P \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x))))"
def "post" \<equiv> "(R \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x))))"
def "tuple" \<equiv> "(p, sp, pre, c#l, post)"
fix s::vhdl_state
assume a3: "pre_of_tuple tuple s"
then have "(P \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x)))) s" 
  unfolding pre_of_tuple_def tuple_def pre_def post_def by auto
then show "post_of_tuple tuple (fst (exec_seq_stmt_list
            (proc_of_tuple tuple) (cmd_of_tuple tuple) (sp_of_tuple tuple) s))"
  proof -
    from a3 have f1: "P s \<and> \<not> (snd (next_flag s)) \<and> \<not> (snd (exit_flag s))"
      unfolding pre_of_tuple_def tuple_def pre_def asst_and_def
      by auto
    from a1 a3 have "(Q \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x)))) 
      (fst (exec_seq_stmt_list p [c] sp s))"
      unfolding valid_hoare_tuple_def proc_of_tuple_def cmd_of_tuple_def 
      sp_of_tuple_def tuple_def pre_of_tuple_def post_of_tuple_def 
      post_def pre_def c_def
      by auto
    then have "post (fst (exec_seq_stmt_list p l sp (fst (exec_seq_stmt_list p [c] sp s))))"
      using a2 unfolding valid_hoare_tuple_def proc_of_tuple_def cmd_of_tuple_def 
      sp_of_tuple_def tuple_def pre_of_tuple_def post_of_tuple_def post_def
      by auto
    then have "post (fst (exec_seq_stmt_list p (c#l) sp s))"
      unfolding post_def c_def using f1 
      by auto
    then show ?thesis
      unfolding proc_of_tuple_def cmd_of_tuple_def sp_of_tuple_def 
      tuple_def post_of_tuple_def pre_def post_def
      by auto
  qed
qed

text {* Hoare logical rule for if statement. 
We assume that the flags for next and exit are both false,
otherwise the statement won't be executed. *}

lemma if_stmt: 
assumes a1: "valid_hoare_tuple (p,sp,
(P \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x))) \<sqinter> 
  (\<lambda>x. (state_val_exp_t c x = Some (val_b True)))),
l1,
(Q \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x)))))"
and a2: "valid_hoare_tuple (p,sp,
(P \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x))) \<sqinter> 
  (\<lambda>x. (state_val_exp_t c x \<noteq> Some (val_b True)))),
l2,
(Q \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x)))))"
shows "valid_hoare_tuple (p,sp,
(P \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x)))),
[sst_if n c l1 l2],
(Q \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x)))))"
unfolding valid_hoare_tuple_def 
apply auto
proof -
def "pre" \<equiv> "P \<sqinter> (\<lambda>x. \<not> snd (next_flag x)) \<sqinter> (\<lambda>x. \<not> snd (exit_flag x))"
def "post" \<equiv> "Q \<sqinter> (\<lambda>x. \<not> snd (next_flag x)) \<sqinter> (\<lambda>x. \<not> snd (exit_flag x))"
def "tuple" \<equiv> "(p, sp, pre, [sst_if n c l1 l2], post)"
fix s::vhdl_state
assume a3: "pre_of_tuple tuple s"
then have "pre s" unfolding pre_of_tuple_def tuple_def by auto
then have f2: "P s \<and> \<not> snd (next_flag s) \<and> \<not> snd (exit_flag s)"
unfolding pre_def asst_and_def by auto
then show "post_of_tuple tuple (fst (exec_seq_stmt_list
            (proc_of_tuple tuple) (cmd_of_tuple tuple) (sp_of_tuple tuple) s))"
  proof (cases "(state_val_exp_t c s = Some (val_b True))")
    case True
    then have f1: "(state_val_exp_t c s = Some (val_b True))" by auto       
    then have "(P \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x))) \<sqinter> 
      (\<lambda>x. (state_val_exp_t c x = Some (val_b True)))) s"
      using f2 unfolding asst_and_def by auto
    then have "(Q \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x))))
      (fst (exec_seq_stmt_list p l1 sp s))"
      using a1 unfolding valid_hoare_tuple_def pre_of_tuple_def post_of_tuple_def
      proc_of_tuple_def cmd_of_tuple_def sp_of_tuple_def by auto
    then have "(Q \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x))))
      (fst (exec_seq_stmt_list p [sst_if n c l1 l2] sp s))"
      using f1 f2 by auto
    then show ?thesis 
      unfolding cmd_of_tuple_def tuple_def post_of_tuple_def post_def
      proc_of_tuple_def sp_of_tuple_def by auto
  next
    case False
    then have f1: "(state_val_exp_t c s \<noteq> Some (val_b True))" by auto  
    then have "(P \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x))) \<sqinter> 
      (\<lambda>x. (state_val_exp_t c x \<noteq> Some (val_b True)))) s"
      using f2 unfolding asst_and_def by auto
    then have "(Q \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x))))
      (fst (exec_seq_stmt_list p l2 sp s))"
      using a2 unfolding valid_hoare_tuple_def pre_of_tuple_def post_of_tuple_def
      proc_of_tuple_def cmd_of_tuple_def sp_of_tuple_def by auto
    then have "(Q \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x))))
      (fst (exec_seq_stmt_list p [sst_if n c l1 l2] sp s))"
      using f1 f2 
      apply auto
      apply (cases "state_val_exp_t c s")
       apply auto
      apply (case_tac "a")
            by auto      
    then show ?thesis 
      unfolding cmd_of_tuple_def tuple_def post_of_tuple_def post_def
      proc_of_tuple_def sp_of_tuple_def by auto
  qed  
qed

text {* Sequential rule in the case of if statement. *}

lemma if_stmt_seq: 
assumes a1: "valid_hoare_tuple (p,sp,
(P \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x)))),
[sst_if n c l1 l2],
(Q \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x)))))"
and a2: "valid_hoare_tuple (p,sp,
(Q \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x)))),
l,
(R\<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x)))))"
shows "valid_hoare_tuple (p,sp,
(P \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x)))),
(sst_if n c l1 l2)#l,
(R \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x)))))"
unfolding valid_hoare_tuple_def
apply auto 
proof -
def "c" \<equiv> "sst_if n c l1 l2"
def "pre" \<equiv> "(P \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x))))"
def "post" \<equiv> "(R \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x))))"
def "tuple" \<equiv> "(p, sp, pre, c#l, post)"
fix s::vhdl_state
assume a3: "pre_of_tuple tuple s"
then have "(P \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x)))) s" 
  unfolding pre_of_tuple_def tuple_def pre_def post_def by auto
then show "post_of_tuple tuple (fst (exec_seq_stmt_list
            (proc_of_tuple tuple) (cmd_of_tuple tuple) (sp_of_tuple tuple) s))"
  proof -
    from a3 have f1: "P s \<and> \<not> (snd (next_flag s)) \<and> \<not> (snd (exit_flag s))"
      unfolding pre_of_tuple_def tuple_def pre_def asst_and_def
      by auto
    from a1 a3 have "(Q \<sqinter> (\<lambda>x. \<not> (snd (next_flag x))) \<sqinter> (\<lambda>x. \<not>(snd (exit_flag x)))) 
      (fst (exec_seq_stmt_list p [c] sp s))"
      unfolding valid_hoare_tuple_def proc_of_tuple_def cmd_of_tuple_def 
      sp_of_tuple_def tuple_def pre_of_tuple_def post_of_tuple_def 
      post_def pre_def c_def
      by auto
    then have "post (fst (exec_seq_stmt_list p l sp (fst (exec_seq_stmt_list p [c] sp s))))"
      using a2 unfolding valid_hoare_tuple_def proc_of_tuple_def cmd_of_tuple_def 
      sp_of_tuple_def tuple_def pre_of_tuple_def post_of_tuple_def post_def
      by auto
    then have "post (fst (exec_seq_stmt_list p (c#l) sp s))"
      unfolding post_def c_def using f1 
      by auto
    then show ?thesis
      unfolding proc_of_tuple_def cmd_of_tuple_def sp_of_tuple_def 
      tuple_def post_of_tuple_def pre_def post_def
      by auto
  qed
qed

text {* The consequence rule. *}

lemma consequence: 
assumes a1: "\<forall>x. P' x \<longrightarrow> P x"
assumes a2: "valid_hoare_tuple (p,sp,P,l,Q)"
assumes a3: "\<forall>x. Q x \<longrightarrow> Q' x"
shows "valid_hoare_tuple (p,sp,P',l,Q')"
proof -
  show ?thesis using a1 a2 a3
    unfolding valid_hoare_tuple_def pre_of_tuple_def post_of_tuple_def
    cmd_of_tuple_def proc_of_tuple_def sp_of_tuple_def
    by auto    
qed

text {* Hoare-style semantics for update_sigprt. *}

definition valid_update_sigprt:: "sigprt list \<Rightarrow> asst \<Rightarrow> asst \<Rightarrow> bool" where
"valid_update_sigprt spl P Q \<equiv> 
  \<forall>x y. ((P x \<and> y = update_sigprt spl x) \<longrightarrow> Q y)"

lemma update_sigprt_base: "valid_update_sigprt [sp]
(\<lambda>w. Q(w\<lparr>state_sp := (state_sp w)(sp := (state_eff_val w sp))\<rparr>))
Q"
unfolding valid_update_sigprt_def
by auto

lemma update_sigprt_step: 
assumes a1: "valid_update_sigprt [sp] P Q"
assumes a2: "valid_update_sigprt spl Q R"
shows "valid_update_sigprt (sp#spl) P R"
unfolding valid_update_sigprt_def
apply auto
proof -
fix s::vhdl_state
def "s'" \<equiv> "(s\<lparr>state_sp := (state_sp s)(sp := state_eff_val s sp)\<rparr>)"
assume a3: "P s"
then show "R (update_sigprt spl s')" 
  proof -
    from a1 a3 have "Q s'" unfolding valid_update_sigprt_def s'_def
      by auto
    then show ?thesis using a2 unfolding valid_update_sigprt_def
      by auto
  qed
qed

text {* Hoare-style semantics for comp_eff_val. *}

definition valid_comp_eff_val:: "sigprt list \<Rightarrow> vhdl_desc\<Rightarrow> asst \<Rightarrow> asst \<Rightarrow> bool" where
"valid_comp_eff_val spl desc P Q \<equiv> 
  \<forall>x y. ((P x \<and> y = comp_eff_val spl desc x) \<longrightarrow> Q y)"

lemma comp_eff_val_base: "valid_comp_eff_val [sp] desc 
  (\<lambda>w. Q(w\<lparr>state_eff_val := (state_eff_val w)(sp := (get_eff_val sp desc w))\<rparr>)) Q"
unfolding valid_comp_eff_val_def
by auto

lemma comp_eff_val_step: 
assumes a1: "valid_comp_eff_val [sp] desc P Q"
assumes a2: "valid_comp_eff_val spl desc Q R"
shows "valid_comp_eff_val (sp#spl) desc P R"
unfolding valid_comp_eff_val_def
apply auto
proof -
fix s::vhdl_state
def "s'" \<equiv> "(s\<lparr>state_eff_val := (state_eff_val s)(sp := get_eff_val sp desc s)\<rparr>)"
assume a3: "P s"
then show "R (comp_eff_val spl desc s')"
  proof -
    from a1 a3 have "Q s'" unfolding valid_comp_eff_val_def s'_def
      by auto
    then show ?thesis using a2 unfolding valid_comp_eff_val_def
      by auto
  qed
qed

text {* Hoare style semantics for exec_proc_all. *}

definition valid_exec_proc_all:: "conc_stmt_list \<Rightarrow> sigprt list \<Rightarrow> subprogram list \<Rightarrow> 
  asst \<Rightarrow> asst \<Rightarrow> bool" where
"valid_exec_proc_all csl spl spgl P Q \<equiv> 
  \<forall>x y. ((P x \<and> y = exec_proc_all csl spl spgl x) \<longrightarrow> Q y)"

lemma exec_proc_all_base: 
assumes a1: "valid_hoare_tuple ((cst_ps n sensl ssl),spgl,P,ssl,Q)"
assumes a2: "has_active_sigprt sensl spl"
shows "valid_exec_proc_all [cst_ps n sensl ssl] spl spgl P Q"
unfolding valid_exec_proc_all_def
apply (simp add: a2)
using a1 unfolding valid_hoare_tuple_def pre_of_tuple_def proc_of_tuple_def
cmd_of_tuple_def sp_of_tuple_def post_of_tuple_def
by auto

lemma exec_proc_all_base2:
assumes a1: "\<not> (has_active_sigprt sensl spl)"
shows "valid_exec_proc_all [cst_ps n sensl ssl] spl spgl P P"
unfolding valid_exec_proc_all_def
using a1 by auto

lemma exec_proc_all_step:
assumes a1: "valid_exec_proc_all [cst_ps n sensl ssl] spl spgl P Q"
assumes a2: "valid_exec_proc_all cs spl spgl Q R"
shows "valid_exec_proc_all ((cst_ps n sensl ssl)#cs) spl spgl P R"
unfolding valid_exec_proc_all_def
apply auto
 proof -
 fix s::vhdl_state
 def "s'" \<equiv> "(fst (exec_seq_stmt_list (cst_ps n sensl ssl) ssl spgl s))"
 assume a3: "P s"
 assume a4: "has_active_sigprt sensl spl"
 from a3 a4 show "R (exec_proc_all cs spl spgl (fst (exec_seq_stmt_list (cst_ps n sensl ssl) ssl spgl s)))"  
   proof -
    from a1 a3 a4 have "Q s'" unfolding valid_exec_proc_all_def s'_def
      by auto
    then show ?thesis using a2 unfolding valid_exec_proc_all_def s'_def
      by auto      
   qed
 next
 fix s::vhdl_state
 def "s'" \<equiv> "(fst (exec_seq_stmt_list (cst_ps n sensl ssl) ssl spgl s))"
 assume a5: "P s"
 assume a6: "\<not> (has_active_sigprt sensl spl)"
 from a5 a6 show "R (exec_proc_all cs spl spgl s)"
  proof -
    from a1 a5 a6 have "Q s" unfolding valid_exec_proc_all_def s'_def
      by auto
    then show ?thesis using a2 unfolding valid_exec_proc_all_def
      by auto
  qed
 qed

text {* Hoare style semantics for resume_processes. *}

definition valid_resume_processes:: "vhdl_desc \<Rightarrow> sigprt list \<Rightarrow> asst \<Rightarrow> asst \<Rightarrow> bool" where
"valid_resume_processes desc spl P Q \<equiv>
  \<forall>x y. ((P x \<and> y = resume_processes desc spl x) \<longrightarrow> (Q y))"

text {* Auxiliary lemmas in the case of act_sp1 = []. *}

lemma emp_spl_has_active_sigprt: "has_active_sigprt sl [] = False"
apply (induction "sl")
 apply auto
by (simp add: List.member_def)

lemma emp_spl_find_active_process: "find_active_process cs [] = False"
apply (induction "cs")
 apply auto
using emp_spl_has_active_sigprt
by (metis (no_types, lifting) conc_stmt.case conc_stmt.exhaust) 

lemma emp_no_active_proc: "has_active_processes desc [] = False"
unfolding has_active_processes_def 
using emp_spl_find_active_process by auto

text {* Here we prove a simplified version: when signals in any processes'
sensitivity list are unchanged, the act_sp1 in resume_processes will be empty.
Assuming this is true, then resume_processes will not do recursive calls. *}

lemma resume_processes_no_rec: 
assumes a1: "valid_exec_proc_all (fst (snd (snd desc))) spl (snd (snd (snd desc))) P Q"
assumes a2: "valid_comp_eff_val (env_sp (fst desc)) desc Q (R \<sqinter> (\<lambda>x. active_sigprts desc x = []))"
assumes a3: "valid_update_sigprt (env_sp (fst desc)) (R \<sqinter> (\<lambda>x. active_sigprts desc x = [])) S"
shows "valid_resume_processes desc spl P S"
unfolding valid_resume_processes_def
apply auto
proof -
fix s::vhdl_state
def "exe" \<equiv> "exec_proc_all (fst (snd (snd desc))) spl (snd (snd (snd desc))) s"
def "eff" \<equiv> "comp_eff_val (env_sp (fst desc)) desc exe"
def "up" \<equiv> "update_sigprt (env_sp (fst desc)) eff"
assume a4: "P s"  
then show "S (let state2 = eff;
                  act_sp1 = active_sigprts desc state2; 
                  state3 = update_sigprt (env_sp (fst desc)) state2
              in 
              if has_active_processes desc act_sp1 then resume_processes desc act_sp1 state3 
              else state3)"
  proof -
    from a1 a4 have "Q exe" 
      unfolding valid_exec_proc_all_def exe_def
      by auto
    then have a5: "(R \<sqinter> (\<lambda>x. active_sigprts desc x = [])) eff"
      using a2 unfolding valid_comp_eff_val_def exe_def eff_def
      by auto
    then have "S (update_sigprt (env_sp (fst desc)) eff)"
      using a3 unfolding valid_update_sigprt_def eff_def exe_def
      by auto
    then have "S (let state2 = eff;
                  act_sp1 = active_sigprts desc state2; 
                  state3 = update_sigprt (env_sp (fst desc)) state2
              in state3)"
      by auto
    then have "S (let state2 = eff;
                  act_sp1 = []; 
                  state3 = update_sigprt (env_sp (fst desc)) state2
              in state3)"
      using a5 by auto
    then have "S (let state2 = eff;
                  act_sp1 = []; 
                  state3 = update_sigprt (env_sp (fst desc)) state2
              in 
              if has_active_processes desc act_sp1 then resume_processes desc act_sp1 state3 
              else state3)"
      using emp_no_active_proc by auto 
    then show ?thesis using a5 unfolding eff_def exe_def
      by (simp add: asst_and_def)       
  qed
qed

text {* Hoare style rules for exec_sim_cyc. *}

definition valid_exec_sim_cyc:: "vhdl_desc \<Rightarrow> vhdl_state \<Rightarrow> asst \<Rightarrow> asst \<Rightarrow> bool" where
"valid_exec_sim_cyc desc s P Q \<equiv> 
\<forall>y. (P s \<and> y = exec_sim_cyc desc s) \<longrightarrow> Q y"

lemma exec_sim_cyc_no_act: 
"valid_exec_sim_cyc desc state
(P \<sqinter> (\<lambda>x. \<not> (has_active_processes desc (active_sigprts desc x)))) 
(P \<sqinter> (\<lambda>x. \<not> (has_active_processes desc (active_sigprts desc x))))"
unfolding valid_exec_sim_cyc_def asst_and_def
by (simp add: exec_sim_cyc_def)

lemma exec_sim_cyc_act:
assumes a1: "valid_resume_processes desc (active_sigprts desc state)
(P \<sqinter> (\<lambda>x. (has_active_processes desc (active_sigprts desc x)))) Q"
shows "valid_exec_sim_cyc desc state
(P \<sqinter> (\<lambda>x. (has_active_processes desc (active_sigprts desc x)))) Q"
unfolding valid_exec_sim_cyc_def
apply auto
proof -
assume "(P \<sqinter> (\<lambda>x. has_active_processes desc (active_sigprts desc x))) state"
then show "Q (exec_sim_cyc desc state)" using a1 unfolding valid_resume_processes_def
  by (auto simp add: exec_sim_cyc_def asst_and_def)  
qed

end