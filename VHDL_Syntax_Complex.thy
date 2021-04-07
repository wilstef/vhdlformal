(*
 * Copyright 2016, NTU
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * Author: Zhe Hou.
 *)

theory VHDL_Syntax_Complex
imports Main VHDL_Types VHDL_Semantics
begin

text {* This file defines more complex syntax used in VHDL designs. 
These syntax are translated to the core syntax in vhdl_syntax.thy. *}

text {* Generate a vector of std_logic values of length n. *}

primrec std_logic_vec_gen:: "nat \<Rightarrow> val \<Rightarrow> val list" where
"std_logic_vec_gen 0 v = []"
|"std_logic_vec_gen (Suc n) v = v#(std_logic_vec_gen n v)"

text {* First we define null signal/port/variable. *}

definition null_port:: "port" where
"null_port \<equiv> (''NULL'', vhdl_integer, mode_out, unconnected, exp_con (vhdl_integer, val_null))"

definition null_signal:: "signal" where
"null_signal \<equiv> (''NULL'', vhdl_integer, register, exp_con (vhdl_integer, val_null))"

definition null_variable:: "variable" where
"null_variable \<equiv> (''NULL'', vhdl_integer, exp_con (vhdl_integer, val_null))"

text {* Find a member of the port/signal/variable list by name. *}

primrec port_list_mem:: "port list \<Rightarrow> string \<Rightarrow> port" where
"port_list_mem [] n = null_port"
|"port_list_mem (p#px) n = (if n = (fst p) then p else port_list_mem px n)"

primrec signal_list_mem:: "signal list \<Rightarrow> string \<Rightarrow> signal" where
"signal_list_mem [] n = null_signal"
|"signal_list_mem (s#sx) n = (if n = (fst s) then s else signal_list_mem sx n)"

primrec variable_list_mem:: "variable list \<Rightarrow> string \<Rightarrow> variable" where
"variable_list_mem [] n = null_variable"
|"variable_list_mem (v#vx) n = (if n = (fst v) then v else variable_list_mem vx n)"

type_synonym subprogcall_complex = "(name \<times> (asmt_rhs list) \<times> type)"

text {* A version of more complex syntax for sequential statements 
that is widely used in VHDL designs. 
***** NOTE THAT *****
The discrete_range in for statement must be static. That is, 
the range can only contain constants or macro definitions, 
the latter of which will be represented by a variable whose value 
doesn't change. Therefore we just use the initial value of that variable 
for the value of the macro. 
**********************
We restrict the type of the value of constants and variables in the 
discrete_range to integers. So we will just use + operator over them
for increment. The expression in for statement must be a variable. 
**********************
We assume that for each for loop, the state has a loop parameter (a variable)
for the loop. The initial value of the variable is the left end of the 
discrete_range. When translating a for loop to a while loop,
we will add a variable assignment before the loop to make sure of it.
We will also add a variable assignment in each loop execution for 
increment/decrement. 
***********************
We assume that in an assignment of a record r1 to a record r2,
r1 and r2 must be the same record type. That is, the corresponding lists
have the same length.  
*}

text {* Function call or procedure call. The type of procedure call is emptype. 
The name is the function/procedure name. *}

datatype seq_stmt_complex =
ssc_sa name sp_clhs asmt_rhs ("_: _ <= _")
|ssc_va name v_clhs asmt_rhs ("_: _ := _")
|ssc_if name condition "seq_stmt_complex list" "elseif_complex list" "seq_stmt_complex list" 
  ("_: IF _ THEN _ _ ELSE _ END IF")
|ssc_case name expression "when_complex list" "seq_stmt_complex list"
  ("_: CASE _ IS _ WHEN OTHERS => _ END CASE")
|ssc_while name condition "seq_stmt_complex list" ("_: WHILE _ LOOP _ END LOOP")
|ssc_for name expression discrete_range "seq_stmt_complex list" ("_: FOR _ IN _ LOOP _ END LOOP")
|ssc_fn name v_clhs subprogcall_complex
|ssc_rt name asmt_rhs
|ssc_pc name subprogcall_complex
|ssc_n name name condition ("_: NEXT _ WHEN _")
|ssc_e name name condition ("_: EXIT _ WHEN _")
|ssc_nl ("NULL")
and elseif_complex = ssc_elseif condition "seq_stmt_complex list" ("ELSIF _ THEN _")
and when_complex = ssc_when choices "seq_stmt_complex list" ("WHEN _ => _")

type_synonym subprogram_complex = "(name \<times> designator \<times> parameter_list \<times> (seq_stmt_complex list) \<times> type \<times> local_var_list)"

text {* Get the subprogram from the subprogram call. *}

primrec get_subprog_complex:: "subprogcall_complex \<Rightarrow> subprogram_complex list \<Rightarrow> subprogram_complex option" where
"get_subprog_complex spc [] = None"
|"get_subprog_complex spc (p#px) = (if (fst spc) = (fst p) then Some p else get_subprog_complex spc px)"

text {* Convert an expression to a variable. *}

definition var_of_exp:: "expression \<Rightarrow> variable" where
"var_of_exp e \<equiv> case e of exp_var v \<Rightarrow> v"

text {* Translate the for loop condition. *}

definition trans_for_cond:: "expression \<Rightarrow> discrete_range \<Rightarrow> condition" where
"trans_for_cond e r \<equiv> 
  case r of 
   vhdl_dis_to e1 e2 \<Rightarrow> (bexpl (bexpr e1 [<=] e) [and] (bexpr e [<=] e2))
  |vhdl_dis_downto e1 e2 \<Rightarrow> (bexpl (bexpr e2 [<=] e) [and] (bexpr e [<=] e1))
"

text {* Translate the choices in each case of a case statement. *}

primrec trans_case_choices:: "expression \<Rightarrow> choices \<Rightarrow> expression" where
"trans_case_choices e [] = (exp_con (vhdl_boolean, val_b False))"
|"trans_case_choices e (c#cs) = 
  bexpl (bexpr e [=] c) [or] (trans_case_choices e cs)"

text {* Generate temporary variable assignments for functions with expression arguments. *}

primrec trans_arg_exp:: "parameter_list \<Rightarrow> asmt_rhs list \<Rightarrow> seq_stmt list" where
"trans_arg_exp [] l2 = []"
|"trans_arg_exp (p#px) l2 = (
  if (fst (snd p)) \<in> {dir_in, dir_inout} then
    (sst_va '''' (fst p) (hd l2))#(trans_arg_exp px (tl l2))
  else (trans_arg_exp px (tl l2))
)"

text {* Convert a subprogramcall_complex to a subprogramcall 
simply by copying the arguments of the subprogram to the parameters in the call. *}

primrec v_clhs_list_of_para_list:: "parameter_list \<Rightarrow> v_clhs list" where
"v_clhs_list_of_para_list [] = []"
|"v_clhs_list_of_para_list (p#px) = (fst p)#(v_clhs_list_of_para_list px)"

definition spcall_of_spcall_complex:: "subprogram_complex \<Rightarrow> 
  subprogcall_complex \<Rightarrow> subprogcall" where
"spcall_of_spcall_complex prog cc \<equiv> 
  ((fst cc),(v_clhs_list_of_para_list (fst (snd (snd prog)))),(snd (snd cc)))"

text {* A translation from the complex syntax to the core syntax. 
We don't translate functional calls and procedure calls here. *}

function trans_seq_complex:: "subprogram_complex list \<Rightarrow> seq_stmt_complex list \<Rightarrow> seq_stmt list" 
and trans_elselist:: "subprogram_complex list \<Rightarrow> elseif_complex list \<Rightarrow> seq_stmt_complex list \<Rightarrow> seq_stmt list" 
and trans_case:: "subprogram_complex list \<Rightarrow> expression \<Rightarrow> when_complex list \<Rightarrow> seq_stmt_complex list \<Rightarrow> seq_stmt list" where
"trans_seq_complex subps [] = []"
|"trans_seq_complex subps (s#sx) = (
  case s of 
  ssc_sa n lhs rhs \<Rightarrow> (sst_sa n lhs rhs)#(trans_seq_complex subps sx)
  |ssc_va n lhs rhs \<Rightarrow> (sst_va n lhs rhs)#(trans_seq_complex subps sx)
  |ssc_if n c sscl1 elsel sscl2 \<Rightarrow> 
    (sst_if n c (trans_seq_complex subps sscl1) (trans_elselist subps elsel sscl2))#(trans_seq_complex subps sx)
  |ssc_case n e whenl sscl \<Rightarrow> (
    case whenl of [] \<Rightarrow> (sst_nl)#(trans_seq_complex subps sx) (* This case statement is illegal. *)
    |x#xs \<Rightarrow> (
      case x of ssc_when cs sscl1 \<Rightarrow>
        (sst_if n (trans_case_choices e cs) 
          (trans_seq_complex subps sscl1) (trans_case subps e xs sscl))#(trans_seq_complex subps sx)
    )
  )
  |ssc_while n c sscl \<Rightarrow> (sst_l n c (trans_seq_complex subps sscl))#(trans_seq_complex subps sx)
  |ssc_for n e r sscl \<Rightarrow> (
    case r of 
     vhdl_dis_to e1 e2 \<Rightarrow>
      (sst_va '''' (clhs_v (lhs_v (var_of_exp e))) (rhs_e e1)) (* Assign the initial value for the loop parameter. *)
      #(sst_l n (trans_for_cond e r) ((trans_seq_complex subps sscl)
        @[sst_va '''' (clhs_v (lhs_v (var_of_exp e))) (* Increment the loop parameter at the end of each loop. *)
          (rhs_e (bexpa e [+] (exp_con (vhdl_integer, (val_i 1)))))]))
      #(trans_seq_complex subps sx)
    |vhdl_dis_downto e1 e2 \<Rightarrow> 
      (sst_va '''' (clhs_v (lhs_v (var_of_exp e))) (rhs_e e1)) (* Assign the initial value for the loop parameter. *)
      #(sst_l n (trans_for_cond e r) ((trans_seq_complex subps sscl)
        @[sst_va '''' (clhs_v (lhs_v (var_of_exp e))) (* Decrement the loop parameter at the end of each loop. *)
          (rhs_e (bexpa e [-] (exp_con (vhdl_integer, (val_i 1)))))]))
      #(trans_seq_complex subps sx)
  )
  |ssc_fn n v subpc \<Rightarrow> (case get_subprog_complex subpc subps of None \<Rightarrow> (trans_seq_complex subps sx)
    |Some prog \<Rightarrow> (
      let sts = trans_arg_exp (fst (snd (snd prog))) (fst (snd subpc)) in
      sts@[(sst_fn n v (spcall_of_spcall_complex prog subpc))]@(trans_seq_complex subps sx)
    )
  )
  |ssc_rt n e \<Rightarrow> (sst_rt n e)#(trans_seq_complex subps sx)
  |ssc_pc n subpc \<Rightarrow> (case get_subprog_complex subpc subps of None \<Rightarrow> (trans_seq_complex subps sx)
    |Some prog \<Rightarrow> (
      let sts = trans_arg_exp (fst (snd (snd prog))) (fst (snd subpc)) in
      sts@[(sst_pc n (spcall_of_spcall_complex prog subpc))]@(trans_seq_complex subps sx)
    )
  )
  |ssc_n n1 n2 c \<Rightarrow> (sst_n n1 n2 c)#(trans_seq_complex subps sx)
  |ssc_e n1 n2 c \<Rightarrow> (sst_e n1 n2 c)#(trans_seq_complex subps sx)
  |ssc_nl \<Rightarrow> (sst_nl)#(trans_seq_complex subps sx))"
|"trans_elselist subps [] sscl2 = trans_seq_complex subps sscl2"
|"trans_elselist subps (x#xs) sscl2 = (
  case x of ssc_elseif c sscl \<Rightarrow>
    [sst_if '''' c (trans_seq_complex subps sscl) (trans_elselist subps xs sscl2)])"
|"trans_case subps e [] sscl = trans_seq_complex subps sscl"
|"trans_case subps e (w#ws) sscl = (
  case w of ssc_when w sscl1 \<Rightarrow> 
    [sst_if '''' (trans_case_choices e w) (trans_seq_complex subps sscl1) (trans_case subps e ws sscl)]
)"
by pat_completeness auto
termination sorry

text {* The "when" conditions in conditional concurrent signal assignment. *}

datatype casmt_rhs =
as_when asmt_rhs condition ("_ WHEN _ ELSE")

text {* The two types of generate statement. 
***** NOTE THAT *****
The discrete_range in generate statement must be static. That is, 
the range can only contain constants or macro definitions, 
the latter of which will be represented by a variable whose value 
doesn't change. Therefore we just use the initial value of that variable 
for the value of the macro. 
**********************
We restrict the type of the value of constants and variables in the 
discrete_range to integers. So we will just use + and - operator over them
for increment and decrement. The expression in for_gen must be a variable. 
*}

datatype gen_type = 
for_gen expression discrete_range ("FOR _ IN _ GENERATE")
|if_gen expression ("IF _ GENERATE")

text {* A version of more complex syntax for concurrent statements. *}

datatype conc_stmt_complex =
csc_ps name sensitivity_list "seq_stmt_complex list" ("_: PROCESS (_) BEGIN _ END PROCESS")
|csc_ca name sp_clhs "casmt_rhs list" asmt_rhs ("_: _ <= <_> _")
|csc_gen name gen_type "conc_stmt_complex list" ("_: _ BEGIN _ END GENERATE")

text {* Translate a (complex) process statement to the original form of 
process statement. *}

definition trans_process_complex:: "subprogram_complex list \<Rightarrow> conc_stmt_complex \<Rightarrow> conc_stmt" where
"trans_process_complex subps csc \<equiv>
  case csc of 
   csc_ps n sl sscl \<Rightarrow> cst_ps n sl (trans_seq_complex subps sscl)
  |_ \<Rightarrow> cst_ps '''' [] [sst_nl]
"

text {* Get the list of signals/ports that are mentioned in the expression. *}

fun sens_of_exp:: "expression \<Rightarrow> sensitivity_list" 
and sens_of_rhsl:: "rhsl list \<Rightarrow> sensitivity_list" where
"sens_of_exp (uexp opr e) = sens_of_exp e"
|"sens_of_exp (bexpl e1 opr e2) = (sens_of_exp e1)@(sens_of_exp e2)"
|"sens_of_exp (bexpr e1 opr e2) = (sens_of_exp e1)@(sens_of_exp e2)"
|"sens_of_exp (bexps e1 opr e2) = (sens_of_exp e1)@(sens_of_exp e2)"
|"sens_of_exp (bexpa e1 opr e2) = (sens_of_exp e1)@(sens_of_exp e2)"
|"sens_of_exp (exp_sig s) = [sp_s s]"
|"sens_of_exp (exp_prt p) = [sp_p p]"
|"sens_of_exp (exp_var v) = []"
|"sens_of_exp (exp_con c) = []"
|"sens_of_exp (exp_nth e e2) = sens_of_exp e"
|"sens_of_exp (exp_sl e1 e2 e3) = sens_of_exp e1"
|"sens_of_exp (exp_tl e) = sens_of_exp e"
|"sens_of_exp (exp_trl e) = sens_of_exp e"
|"sens_of_exp (exp_fc fc) = []" (* We don't care about function arguments at the moment. *)
|"sens_of_exp (exp_r r) = sens_of_rhsl [r]"
|"sens_of_rhsl [] = []"
|"sens_of_rhsl (r#rx) = (case r of
  (rl_s s) \<Rightarrow> [sp_s s]@(sens_of_rhsl rx)
  |(rl_p p) \<Rightarrow> [sp_p p]@(sens_of_rhsl rx)
  |(rl_v v) \<Rightarrow> (sens_of_rhsl rx)
  |(rnl l) \<Rightarrow> (sens_of_rhsl l)@(sens_of_rhsl rx)
)"

text {* Find the sensitivity list from the "when" conditions. *}

primrec get_sens_csa:: "casmt_rhs list \<Rightarrow> sensitivity_list" where
"get_sens_csa [] = []"
|"get_sens_csa (w#wx) = (
  case w of as_when rhs c \<Rightarrow>
   (sens_of_exp c)@(get_sens_csa wx)
)"

text {* Translate the "when" list to a "elseif" list. *}

primrec when_list_to_elseif_list:: "casmt_rhs list \<Rightarrow> sp_clhs \<Rightarrow> elseif_complex list" where
"when_list_to_elseif_list [] lhs = []"
|"when_list_to_elseif_list (w#wx) lhs = (
  case w of as_when rhs c \<Rightarrow> 
    (ELSIF c THEN ['''': lhs <= rhs])#(when_list_to_elseif_list wx lhs)
)"

definition trans_when_list:: "sp_clhs \<Rightarrow> casmt_rhs list \<Rightarrow> asmt_rhs \<Rightarrow> seq_stmt_complex" where
"trans_when_list lhs whenl rhs \<equiv>
  if length whenl \<le> 0 then (* There're no when conditions. *)
    (* Translate the sequential signal assignment. *)
    ('''': lhs <= rhs)
  else (* There are when conditions. Translate to a If statement. *)
    case hd whenl of as_when rhs1 c1 \<Rightarrow> 
      ('''': IF c1 THEN ['''': lhs <= rhs1] 
             (when_list_to_elseif_list (tl whenl) lhs) 
             ELSE ['''': lhs <= rhs] 
             END IF)
"

text {* Translate conditional concurrent signal assignment to
a process statement (possibly) with a if statement. *}

definition trans_conc_sig_asgn:: "subprogram_complex list \<Rightarrow> conc_stmt_complex \<Rightarrow> conc_stmt" where
"trans_conc_sig_asgn subps csc \<equiv>
  case csc of csc_ca n lhs whenl rhs \<Rightarrow> 
    cst_ps n (get_sens_csa whenl) 
      (trans_seq_complex subps [trans_when_list lhs whenl rhs])
  |_ \<Rightarrow> cst_ps '''' [] [sst_nl]
"

text {* Convert an expression to a signal/port type. *}

definition sig_of_exp:: "expression \<Rightarrow> signal" where
"sig_of_exp e \<equiv> case e of exp_sig s \<Rightarrow> s"

definition prt_of_exp:: "expression \<Rightarrow> port" where
"prt_of_exp e \<equiv> case e of exp_prt p \<Rightarrow> p"

text {* Substitute expressions e1 with e2 in an expression e. *}

fun exp_sub:: "expression \<Rightarrow> expression \<Rightarrow> expression \<Rightarrow> expression"
and rhsl_sub:: "expression \<Rightarrow> expression \<Rightarrow> rhsl \<Rightarrow> rhsl" where
"exp_sub e1 e2 (uexp opr e) = (
  if (uexp opr e) = e1 then e2 
  else uexp opr (exp_sub e1 e2 e))"
|"exp_sub e1 e2 (bexpl e3 opr e4) = (
  if (bexpl e3 opr e4) = e1 then e2 
  else bexpl (exp_sub e1 e2 e3) opr (exp_sub e1 e2 e4))"
|"exp_sub e1 e2 (bexpr e3 opr e4) = (
  if (bexpr e3 opr e4) = e1 then e2 
  else bexpr (exp_sub e1 e2 e3) opr (exp_sub e1 e2 e4))"
|"exp_sub e1 e2 (bexps e3 opr e4) = (
  if (bexps e3 opr e4) = e1 then e2
  else bexps (exp_sub e1 e2 e3) opr (exp_sub e1 e2 e4))"
|"exp_sub e1 e2 (bexpa e3 opr e4) = (
  if (bexpa e3 opr e4) = e1 then e2
  else bexpa (exp_sub e1 e2 e3) opr (exp_sub e1 e2 e4))"
|"exp_sub e1 e2 (exp_sig s) = (
  if (exp_sig s) = e1 then e2 
  else exp_sig s)"
|"exp_sub e1 e2 (exp_prt p) = (
  if (exp_prt p) = e1 then e2
  else exp_prt p)"
|"exp_sub e1 e2 (exp_var v) = (
  if (exp_var v) = e1 then e2
  else exp_var v)"
|"exp_sub e1 e2 (exp_con c) = (
  if (exp_con c) = e1 then e2
  else exp_con c)"
|"exp_sub e1 e2 (exp_nth e e3) = (
  if (exp_nth e e3) = e1 then e2
  else exp_nth (exp_sub e1 e2 e) (exp_sub e1 e2 e3))"
|"exp_sub e1 e2 (exp_sl e e3 e4) = (
  if (exp_sl e e3 e4) = e1 then e2
  else exp_sl (exp_sub e1 e2 e) (exp_sub e1 e2 e3) (exp_sub e1 e2 e4)
)"
|"exp_sub e1 e2 (exp_tl e) = (
  if (exp_tl e) = e1 then e2
  else exp_tl (exp_sub e1 e2 e)
)"
|"exp_sub e1 e2 (exp_trl e) = (
  if (exp_trl e) = e1 then e2
  else exp_trl (exp_sub e1 e2 e)
)"
|"exp_sub e1 e2 (exp_fc fc) = (exp_fc fc)" (* We don't care about function calls here. *)
|"exp_sub e1 e2 (exp_r r) = exp_r (rhsl_sub e1 e2 r)"
|"rhsl_sub e1 e2 (rl_s s) = rl_s (sig_of_exp (exp_sub e1 e2 (exp_sig s)))"
|"rhsl_sub e1 e2 (rl_p p) = rl_s (sig_of_exp (exp_sub e1 e2 (exp_prt p)))"
|"rhsl_sub e1 e2 (rl_v v) = rl_s (sig_of_exp (exp_sub e1 e2 (exp_var v)))"
|"rhsl_sub e1 e2 (rnl []) = rnl []"
|"rhsl_sub e1 e2 (rnl (x#xs)) = rnl ((rhsl_sub e1 e2 x)#(list_of_rhsl (rhsl_sub e1 e2 (rnl xs))))"

text {* Substitute expressions e1 with e2 in a list of expressions. *}

definition expl_sub:: "expression \<Rightarrow> expression \<Rightarrow> expression list\<Rightarrow> expression list" where
"expl_sub e1 e2 el \<equiv> map (exp_sub e1 e2) el"

text {* Convert a sigprt type to an expression. And vice versa. *}

definition exp_of_sigprt:: "sigprt \<Rightarrow> expression" where
"exp_of_sigprt sp \<equiv> case sp of sp_s s \<Rightarrow> exp_sig s |sp_p p \<Rightarrow> exp_prt p"

definition sigprt_of_exp:: "expression \<Rightarrow> sigprt" where
"sigprt_of_exp e \<equiv> case e of exp_sig s \<Rightarrow> sp_s s | exp_prt p \<Rightarrow> sp_p p"

text {* Substitute expressions e1 with e2 in a discrete_range r. *}

definition dis_range_sub:: "expression \<Rightarrow> expression \<Rightarrow> discrete_range \<Rightarrow> discrete_range" where
"dis_range_sub e1 e2 r \<equiv>
  case r of vhdl_dis_to e3 e4 \<Rightarrow> vhdl_dis_to (exp_sub e1 e2 e3) (exp_sub e1 e2 e4)
  |vhdl_dis_downto e3 e4 \<Rightarrow> vhdl_dis_downto (exp_sub e1 e2 e3) (exp_sub e1 e2 e4)"

text {* Substitute expressions e1 with e2 in a asmt_rhs. *}

definition asmt_rhs_sub:: "expression \<Rightarrow> expression \<Rightarrow> asmt_rhs \<Rightarrow> asmt_rhs" where
"asmt_rhs_sub e1 e2 rhs \<equiv>
  case rhs of rhs_e e \<Rightarrow> (rhs_e (exp_sub e1 e2 e))
  |rhs_o e \<Rightarrow> (rhs_o (exp_sub e1 e2 e))"

text {* Substitute expressions e1 with e2 in a sigprt. *}

definition sigprt_sub:: "expression \<Rightarrow> expression \<Rightarrow> sigprt \<Rightarrow> sigprt" where
"sigprt_sub e1 e2 sp \<equiv> sigprt_of_exp (exp_sub e1 e2 (exp_of_sigprt sp))"

text {* Substitute expressions e1 with e2 in a list of sigprt. *}

definition sigprtl_sub:: "expression \<Rightarrow> expression \<Rightarrow> sigprt list \<Rightarrow> sigprt list " where
"sigprtl_sub e1 e2 spl \<equiv> map (sigprt_sub e1 e2) spl"

text {* Substitute expressions e1 with e2 in a variable. *}

definition var_sub:: "expression \<Rightarrow> expression \<Rightarrow> variable \<Rightarrow> variable" where
"var_sub e1 e2 v \<equiv> var_of_exp (exp_sub e1 e2 (exp_var v))"

text {* Substitute expressions e1 with e2 in a spl and rhsl. *}
(*
primrec sl_sub:: "expression \<Rightarrow> expression \<Rightarrow> signal list \<Rightarrow> signal list" where
"sl_sub e1 e2 [] = []"
|"sl_sub e1 e2 (s#sx) = (sig_of_exp (exp_sub e1 e2 (exp_sig s)))#(sl_sub e1 e2 sx)"

primrec pl_sub:: "expression \<Rightarrow> expression \<Rightarrow> port list \<Rightarrow> port list" where
"pl_sub e1 e2 [] = []"
|"pl_sub e1 e2 (p#px) = (prt_of_exp (exp_sub e1 e2 (exp_prt p)))#(pl_sub e1 e2 px)"

definition vl_sub:: "expression \<Rightarrow> expression \<Rightarrow> variable list \<Rightarrow> variable list" where
"vl_sub e1 e2 vl \<equiv> map (var_sub e1 e2) vl"*)

fun spl_sub:: "expression \<Rightarrow> expression \<Rightarrow> spl \<Rightarrow> spl" where
"spl_sub e1 e2 (spl_s s) = spl_s (sig_of_exp (exp_sub e1 e2 (exp_sig s)))"
|"spl_sub e1 e2 (spl_p p) = spl_p (prt_of_exp (exp_sub e1 e2 (exp_prt p)))"
|"spl_sub e1 e2 (spnl nl1) = (
  case nl1 of (n,[]) \<Rightarrow> spnl (n,[])
  |(n,(x#xs)) \<Rightarrow> spnl (n,((spl_sub e1 e2 x)#(list_of_spl (spl_sub e1 e2 (spnl (n,xs))))))
)"

fun vl_sub:: "expression \<Rightarrow> expression \<Rightarrow> vl \<Rightarrow> vl" where
"vl_sub e1 e2 (vl_v v) = vl_v (var_sub e1 e2 v)"
|"vl_sub e1 e2 (vnl nl1) = (
  case nl1 of (n,[]) \<Rightarrow> vnl (n,[])
  |(n,(x#xs)) \<Rightarrow> vnl (n,((vl_sub e1 e2 x)#(list_of_vl (vl_sub e1 e2 (vnl (n,xs))))))
)"

text {* Substitute expressions e1 with e2 in a seq_stmt_complex. *}

function seq_stmt_complex_sub:: "expression \<Rightarrow> expression \<Rightarrow> seq_stmt_complex list \<Rightarrow>
  seq_stmt_complex list" 
and elselist_sub:: "expression \<Rightarrow> expression \<Rightarrow> elseif_complex list \<Rightarrow> 
  elseif_complex list" 
and whenlist_sub:: "expression \<Rightarrow> expression \<Rightarrow> when_complex list \<Rightarrow> 
  when_complex list" where
"seq_stmt_complex_sub e1 e2 [] = []"
|"seq_stmt_complex_sub e1 e2 (s#sx) = (
  case s of 
  ssc_sa n (clhs_sp (lhs_s sp)) rhs \<Rightarrow> (ssc_sa n (clhs_sp (lhs_s (sigprt_sub e1 e2 sp))) (asmt_rhs_sub e1 e2 rhs))
                     #(seq_stmt_complex_sub e1 e2 sx)
  |ssc_sa n (clhs_sp (lhs_sa sp r)) rhs \<Rightarrow> (ssc_sa n (clhs_sp (lhs_sa (sigprt_sub e1 e2 sp) (dis_range_sub e1 e2 r))) 
                          (asmt_rhs_sub e1 e2 rhs))
                         #(seq_stmt_complex_sub e1 e2 sx)
  |ssc_sa n (clhs_spr spl) (rhs_e (exp_r rhsl)) \<Rightarrow> (ssc_sa n (clhs_spr (spl_sub e1 e2 spl)) (rhs_e (exp_r (rhsl_sub e1 e2 rhsl))))
                         #(seq_stmt_complex_sub e1 e2 sx)
  |ssc_va n (clhs_v (lhs_v v)) rhs \<Rightarrow> (ssc_va n (clhs_v (lhs_v (var_sub e1 e2 v))) (asmt_rhs_sub e1 e2 rhs))
                     #(seq_stmt_complex_sub e1 e2 sx)
  |ssc_va n (clhs_v (lhs_va v r)) rhs \<Rightarrow> (ssc_va n (clhs_v (lhs_va (var_sub e1 e2 v) (dis_range_sub e1 e2 r))) 
                          (asmt_rhs_sub e1 e2 rhs))
                        #(seq_stmt_complex_sub e1 e2 sx)
  |ssc_va n (clhs_vr vl) (rhs_e (exp_r rhsl)) \<Rightarrow> (ssc_va n (clhs_vr (vl_sub e1 e2 vl)) (rhs_e (exp_r (rhsl_sub e1 e2 rhsl))))#(seq_stmt_complex_sub e1 e2 sx)                   
  |ssc_if n c sscl1 elsel sscl2 \<Rightarrow> (ssc_if n (exp_sub e1 e2 c) (seq_stmt_complex_sub e1 e2 sscl1) 
                                    (elselist_sub e1 e2 elsel) (seq_stmt_complex_sub e1 e2 sscl2))
                                   #(seq_stmt_complex_sub e1 e2 sx)
  |ssc_case n e whenl sscl \<Rightarrow> (ssc_case n (exp_sub e1 e2 e) (whenlist_sub e1 e2 whenl)
                                (seq_stmt_complex_sub e1 e2 sscl))
                              #(seq_stmt_complex_sub e1 e2 sx)
  |ssc_while n c sscl \<Rightarrow> (ssc_while n (exp_sub e1 e2 c) (seq_stmt_complex_sub e1 e2 sscl))
                         #(seq_stmt_complex_sub e1 e2 sx)
  |ssc_for n e r sscl \<Rightarrow> (ssc_for n (exp_sub e1 e2 e) (dis_range_sub e1 e2 r) 
                          (seq_stmt_complex_sub e1 e2 sscl))
                         #(seq_stmt_complex_sub e1 e2 sx)
  |ssc_n n1 n2 c \<Rightarrow> (ssc_n n1 n2 (exp_sub e1 e2 c))#(seq_stmt_complex_sub e1 e2 sx)
  |ssc_e n1 n2 c \<Rightarrow> (ssc_e n1 n2 (exp_sub e1 e2 c))#(seq_stmt_complex_sub e1 e2 sx)
  |ssc_nl \<Rightarrow> ssc_nl#(seq_stmt_complex_sub e1 e2 sx)
)"
|"elselist_sub e1 e2 [] = []"
|"elselist_sub e1 e2 (e#ex) = (
  case e of ssc_elseif c sscl \<Rightarrow> (ssc_elseif (exp_sub e1 e2 c) (seq_stmt_complex_sub e1 e2 sscl))
                                 #(elselist_sub e1 e2 ex)
)"
|"whenlist_sub e1 e2 [] = []"
|"whenlist_sub e1 e2 (w#wx) = (
  case w of ssc_when el sscl \<Rightarrow> (ssc_when (expl_sub e1 e2 el) (seq_stmt_complex_sub e1 e2 sscl))
                                #(whenlist_sub e1 e2 wx)
)"
by pat_completeness auto        
termination sorry

text {* Substitute expressions e1 with e2 in a process statement. *}

definition csc_ps_sub:: "expression \<Rightarrow> expression \<Rightarrow> conc_stmt_complex 
  \<Rightarrow> conc_stmt_complex" where
"csc_ps_sub e1 e2 c \<equiv> 
  case c of csc_ps n sl sscl \<Rightarrow> (csc_ps n (sigprtl_sub e1 e2 sl) 
    (seq_stmt_complex_sub e1 e2 sscl))"

text {* Substitute expressions e1 with e2 in casmt_rhs. *}

definition casmt_rhs_sub:: "expression \<Rightarrow> expression \<Rightarrow> casmt_rhs \<Rightarrow> casmt_rhs" where
"casmt_rhs_sub e1 e2 crhs \<equiv> 
  case crhs of 
  as_when rhs c \<Rightarrow> as_when (asmt_rhs_sub e1 e2 rhs) (exp_sub e1 e2 c)
(*  |as_when (crhs_r rhs) c \<Rightarrow> as_when (crhs_r (rhsl_sub e1 e2 rhs)) (exp_sub e1 e2 c)*)"

text {* Substitute expressions e1 with e2 in a list of casmt_rhs. *}

definition casmt_rhs_subl:: "expression \<Rightarrow> expression \<Rightarrow> casmt_rhs list   
  \<Rightarrow> casmt_rhs list" where
"casmt_rhs_subl e1 e2 l \<equiv> map (casmt_rhs_sub e1 e2) l"

text {* Substitute expressions e1 with e2 in a concurrent signal assignment. *}

definition csc_ca_sub:: "expression \<Rightarrow> expression \<Rightarrow> conc_stmt_complex 
  \<Rightarrow> conc_stmt_complex" where
"csc_ca_sub e1 e2 c \<equiv>
  case c of csc_ca n (clhs_sp (lhs_s sp)) crhsl rhs \<Rightarrow> 
    csc_ca n (clhs_sp (lhs_s (sigprt_sub e1 e2 sp))) 
    (casmt_rhs_subl e1 e2 crhsl) (asmt_rhs_sub e1 e2 rhs)
  |csc_ca n (clhs_sp (lhs_sa sp r)) crhsl rhs \<Rightarrow> 
    csc_ca n (clhs_sp (lhs_sa (sigprt_sub e1 e2 sp) (dis_range_sub e1 e2 r))) 
    (casmt_rhs_subl e1 e2 crhsl) (asmt_rhs_sub e1 e2 rhs)
  |csc_ca n (clhs_spr l1) crhsl (rhs_e (exp_r l2)) \<Rightarrow> 
    csc_ca n (clhs_spr (spl_sub e1 e2 l1)) 
    (casmt_rhs_subl e1 e2 crhsl) (rhs_e (exp_r (rhsl_sub e1 e2 l2)))"

text {* Substitute expressions e1 with e2 in a gen_type. *}

definition gen_type_sub:: "expression \<Rightarrow> expression \<Rightarrow> gen_type \<Rightarrow> gen_type" where
"gen_type_sub e1 e2 gt \<equiv> 
  case gt of for_gen e r \<Rightarrow> (for_gen (exp_sub e1 e2 e) (dis_range_sub e1 e2 r))
  |if_gen e \<Rightarrow> (if_gen (exp_sub e1 e2 e))"

function conc_stmt_complex_sub:: "expression \<Rightarrow> expression \<Rightarrow> conc_stmt_complex list
  \<Rightarrow> conc_stmt_complex list"  where
"conc_stmt_complex_sub e1 e2 [] = []"
|"conc_stmt_complex_sub e1 e2 (c#cx) = (
  case c of 
   csc_ps n sl sscl \<Rightarrow> (csc_ps_sub e1 e2 c)#(conc_stmt_complex_sub e1 e2 cx)
  |csc_ca n lhs crhsl rhs \<Rightarrow> (csc_ca_sub e1 e2 c)#(conc_stmt_complex_sub e1 e2 cx)
  |csc_gen n gt cscl \<Rightarrow> (csc_gen n (gen_type_sub e1 e2 gt) 
    (conc_stmt_complex_sub e1 e2 cscl))#(conc_stmt_complex_sub e1 e2 cx)
)"
by pat_completeness auto        
termination sorry

function gen_proc:: "expression \<Rightarrow> int \<Rightarrow> int \<Rightarrow> conc_stmt_complex list 
  \<Rightarrow> conc_stmt_complex list" where
"gen_proc e i j cscl = (
  if i > j then (* Stop generating. *)
    []
  else
    (conc_stmt_complex_sub e (exp_con (vhdl_integer,(val_i i))) cscl)
    @(gen_proc e (i+1) j cscl)
)"
by pat_completeness auto
termination 

gen_proc
apply (relation "measure (\<lambda>(e,i,j,cscl). nat (j - i + 1))")
by auto

text {* Translate a generate statement to a list of process statements. 
N.B. the VHDL reference 2000 elaborates a generate statement 
to a list of block statements. But we do not take this route here. *}

function trans_conc_complex:: "subprogram_complex list \<Rightarrow> conc_stmt_complex list \<Rightarrow> conc_stmt list" 
and trans_gen:: "subprogram_complex list \<Rightarrow> conc_stmt_complex \<Rightarrow> conc_stmt list" 
(*and trans_if:: "expression \<Rightarrow> conc_stmt_complex list \<Rightarrow> conc_stmt list"*) 
where
"trans_conc_complex subps [] = []"
|"trans_conc_complex subps (c#cx) = (
  case c of 
   csc_ps n sl sscl \<Rightarrow> (trans_process_complex subps c)#(trans_conc_complex subps cx)
  |csc_ca n sp whenl rhs \<Rightarrow> (trans_conc_sig_asgn subps c)#(trans_conc_complex subps cx)
  |csc_gen n gt cscl \<Rightarrow> (trans_gen subps c)@(trans_conc_complex subps cx)
)"
|"trans_gen subps c = (
  case c of csc_gen n gt cscl \<Rightarrow> (
    case gt of for_gen e r \<Rightarrow> (
      case r of vhdl_dis_to e1 e2 \<Rightarrow> (
        case ((init_val_exp_t e1),(init_val_exp_t e2)) of
         (Some (val_i i),Some (val_i j)) \<Rightarrow> (trans_conc_complex subps (gen_proc e i j cscl))
        |_ \<Rightarrow> [] (* Other types of the range are not supported. *)
      )
      |vhdl_dis_downto e1 e2 \<Rightarrow> (
        case ((init_val_exp_t e1),(init_val_exp_t e2)) of
         (Some (val_i i),Some (val_i j)) \<Rightarrow> (trans_conc_complex subps (gen_proc e j i cscl))
        |_ \<Rightarrow> [] (* Other types of the range are not supported. *)
      )
    )  
    |if_gen e \<Rightarrow> ((*trans_if e cscl*)
      case init_val_exp_t e of 
       Some (val_b True) \<Rightarrow> (trans_conc_complex subps cscl)
      |Some (val_b False) \<Rightarrow> [] 
      |_ \<Rightarrow> [] (* The expression must be of boolean type and have an initial value. *)
    )
  )
)"
by pat_completeness auto        
termination sorry

definition trans_subprog_complex:: "subprogram_complex list \<Rightarrow> subprogram_complex \<Rightarrow> subprogram" where
"trans_subprog_complex subps spc \<equiv> ((fst spc), (fst (snd spc)), (fst (snd (snd spc))), 
 (trans_seq_complex subps (fst (snd (snd (snd spc))))), (fst (snd (snd (snd (snd spc))))), 
 (snd (snd (snd (snd (snd spc))))))"

text {* The definition of vhdl description complex version. *}

type_synonym vhdl_desc_complex = "(environment \<times> res_fn \<times> conc_stmt_complex list \<times> subprogram_complex list)"

(*
text {* Convert a natural to a string. *}

fun string_of_nat :: "nat \<Rightarrow> string"
where
  "string_of_nat n = (if n < 10 then [char_of_nat (48 + n)] else 
     string_of_nat (n div 10) @ [char_of_nat (48 + (n mod 10))])"

text {* Generate a temporary variable with the suffix n. The type and 
initial expression do not matter. *}

definition tmp_var_gen:: "nat \<Rightarrow> variable" where
"tmp_var_gen n \<equiv> ((''isabelle_tmp_''@(string_of_nat n)),
  vhdl_integer,exp_con (vhdl_integer,(val_i 0)))"

text {* Here we deal with function calls as expressions. For each function call 
in an expression in the form
v := f() + ...
we translate it to
tmp := f();
v := tmp + ...
When this translation is finished, there should be no funciton calls as expressions. 
All of them are converted to function call statements. 
*}

text {* If an expression contains a function call, it is translated as above.
The natural is the accumulative number of temporary variables.  
Return the list of statements to be added and the new expression. 
Note that we don't check the expression in signals, ports, and variables,
as those are supposed to be initialisation expression,
and should not contain functions. *}

primrec trans_fun_exp_exp:: "expression \<Rightarrow> nat \<Rightarrow> (nat \<times> seq_stmt_complex list \<times> expression)" where
"trans_fun_exp_exp (uexp opr e) n = trans_fun_exp_exp e n"
|"trans_fun_exp_exp (bexpl e1 opr e2) n = (
  let (n1,st1,e3) = trans_fun_exp_exp e1 n;
      (n2,st2,e4) = trans_fun_exp_exp e2 n1
  in
  (n2,st1@st2,(bexpl e3 opr e4))
)"
|"trans_fun_exp_exp (bexpr e1 opr e2) n = (
  let (n1,st1,e3) = trans_fun_exp_exp e1 n;
      (n2,st2,e4) = trans_fun_exp_exp e2 n1
  in
  (n2,st1@st2,(bexpr e3 opr e4))
)"
|"trans_fun_exp_exp (bexps e1 opr e2) n = (
  let (n1,st1,e3) = trans_fun_exp_exp e1 n;
      (n2,st2,e4) = trans_fun_exp_exp e2 n2
  in
  (n2,st1@st2,(bexps e3 opr e4))
)"
|"trans_fun_exp_exp (bexpa e1 opr e2) n = (
  let (n1,st1,e3) = trans_fun_exp_exp e1 n;
      (n2,st2,e4) = trans_fun_exp_exp e2 n1
  in
  (n2,st1@st2,(bexpa e3 opr e4))
)"
|"trans_fun_exp_exp (exp_sig s) n = (n,[],(exp_sig s))"
|"trans_fun_exp_exp (exp_prt p) n = (n,[],(exp_prt p))"
|"trans_fun_exp_exp (exp_var v) n = (n,[],(exp_var v))"
|"trans_fun_exp_exp (exp_con c) n = (n,[],(exp_con c))"
|"trans_fun_exp_exp (exp_nth e1 e2) n = (
  let (n1,st1,e3) = trans_fun_exp_exp e1 n;
      (n2,st2,e4) = trans_fun_exp_exp e2 n1
  in
  (n2,st1@st2,(exp_nth e3 e4))
)"
|"trans_fun_exp_exp (exp_sl e1 e2 e3) n = (
  let (n1,st1,e4) = trans_fun_exp_exp e1 n;
      (n2,st2,e5) = trans_fun_exp_exp e2 n1;
      (n3,st3,e6) = trans_fun_exp_exp e3 n3
  in
  (n3,st1@st2@st3,(exp_sl e4 e5 e6))
)"
|"trans_fun_exp_exp (exp_tl e1) n = (
  let (n1,st1,e2) = trans_fun_exp_exp e1 n
  in
  (n1,st1,(exp_tl e2))
)"
|"trans_fun_exp_exp (exp_trl e1) n = (
  let (n1,st1,e2) = trans_fun_exp_exp e1 n
  in
  (n1,st1,(exp_trl e2))
)"
|"trans_fun_exp_exp (exp_fc (n,el,t)) n = (
  let v = tmp_var_gen n; 
      st = (ssc_fn '''' () )
  in
)"

definition trans_fun_exp:: "vhdl_desc_complex \<Rightarrow> vhdl_desc_complex" where
"trans_fun_exp desc \<equiv> "
*)

text {* Translate a complex vhdl description to a core version vhdl description. *}

definition trans_vhdl_desc_complex:: "vhdl_desc_complex \<Rightarrow> vhdl_desc" where
"trans_vhdl_desc_complex dc \<equiv> 
  let subps = snd (snd (snd dc)) in
  ((fst dc),(fst (snd dc)),(trans_conc_complex subps (fst (snd (snd dc)))),
   (List.map (trans_subprog_complex subps) (snd (snd (snd dc)))))"

text {* The below are some abbreviations for the convenience of VHDL encoding 
in Isabelle. *}
(* Expression of std_logic. *)
definition "el b \<equiv> exp_con (vhdl_std_logic,(val_c b))"
(* Expression of std_ulogic. *)
definition "eul b \<equiv> exp_con (vhdl_std_ulogic,(val_c b))"
(* Expression of natural. *)
definition "en i \<equiv> exp_con (vhdl_natural,(val_i i))"
(* Expression of std_logic_vector. *)
definition "ell l \<equiv> exp_con (vhdl_std_logic_vector,(val_list l))"
(* Expression of std_ulogic_vector. *)
definition "eull l \<equiv> exp_con (vhdl_std_ulogic_vector,(val_list l))"
(* Expression of std_logic_vector with reversed list. *)
definition "elrl l \<equiv> exp_con (vhdl_std_logic_vector,(val_rlist l))"
(* Expression of std_ulogic_vector with reversed list. *)
definition "eulrl l \<equiv> exp_con (vhdl_std_ulogic_vector,(val_rlist l))"

end