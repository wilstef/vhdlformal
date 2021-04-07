(*
 * Copyright 2016, NTU
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * Author: Zhe Hou.
 *)

theory VHDL_Semantics
imports Main VHDL_Types
begin

text {* This files defines the semantics of the core syntax.
The operational semantics of the signal assignment statement. The assignment
gives a driving value of the signal in the state. 

We need to record that signal_asmt is inside process-stmt.

From [1] page 104: "The driver for a signal s is present in every process statement
that assigns a value to the signal through a signal assignment statement,
and in every process statement that assigns a value to the formal part of the port 
association for the which the signal s is the actual." 

We will treat ports and signals the same here. This is subject to changes. *}

text {* Make a list of expressions e of length n. *}

fun mk_list:: "'a \<Rightarrow> nat \<Rightarrow> 'a list" where
"mk_list e 0 = []"
|"mk_list e n = e#(mk_list e (n-1))"

text {* Assign l2 to a range from i to j in l1. 
The length of l2 must be the same as j - i + 1.
We assume i < j. 
Return a list l1' which has l2 as a part of it from i to j,
but otherwise unchanged. *}

fun assign_range_to:: "val list \<Rightarrow> int \<Rightarrow> int \<Rightarrow> val list \<Rightarrow> val list" where
"assign_range_to [] i j l2 = []"
|"assign_range_to (x#xs) i j [] = x#xs"
|"assign_range_to (x#xs) i j (y#ys) = (
  if i > 0 then (* Add x to the resultant list. *)
    x#(assign_range_to xs (i-1) (j-1) (y#ys))
  else if j \<ge> 0 then (* Add the head of l2 to the resultant list. *)
    y#(assign_range_to xs i (j-1) ys)
  else (* Add xs to the resultant list. *)
    x#xs
)"

text {* Assign l2 to a range from i downto j in l1. 
The length of l2 must be the same as i - j + 1.
We assume i > j. 
Return a list l1' which has l2 as a part of it from i downto j,
but otherwise unchanged. *}

definition assign_range_downto:: "val list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> val list \<Rightarrow> val list" where
"assign_range_downto l1 i j l2 = rev (assign_range_to (rev l1) j i (rev l2))"

text {* Signal assignment. 
Here we DON'T deal with assignment of records, i.e., clhs_spr <= rhs_e (exp_r rhsl). 
Assignment of records is translated to assignment of members in the record. *}

definition exec_sig_asmt:: "conc_stmt \<Rightarrow> seq_stmt \<Rightarrow> vhdl_state \<Rightarrow> vhdl_state" where
"exec_sig_asmt p ss state \<equiv>
  case ss of (sst_sa n lhs rhs) \<Rightarrow> (
    case lhs of  
     clhs_sp (lhs_s sp) \<Rightarrow> (
      case rhs of
       rhs_e e \<Rightarrow> (state\<lparr>state_dr_val := (state_dr_val state)
        (sp := ((state_dr_val state) sp)(p := state_val_exp_t e state))\<rparr>)
      |rhs_o e \<Rightarrow> (  
        case sigprt_init_val sp of Some v \<Rightarrow> (
          case v of val_list vl \<Rightarrow> ( (* sp is a vector. Assign all elements to e. *) 
            case state_val_exp_t e state of None \<Rightarrow> (* e doesn't have a valid value. *)
              (state\<lparr>state_dr_val := (state_dr_val state)
                (sp := ((state_dr_val state) sp)(p := None))\<rparr>)
            |Some vv \<Rightarrow> (* e has a valid value vv. *)
              (state\<lparr>state_dr_val := (state_dr_val state)
                (sp := ((state_dr_val state) sp)
                  (p := Some (val_list (mk_list vv (length vl)))))\<rparr>)
          )
          |val_rlist vl \<Rightarrow> ( (* sp is a vector. Assign all elements to e. *) 
            case state_val_exp_t e state of None \<Rightarrow> (* e doesn't have a valid value. *)
              (state\<lparr>state_dr_val := (state_dr_val state)
                (sp := ((state_dr_val state) sp)(p := None))\<rparr>)
            |Some vv \<Rightarrow> (* e has a valid value vv. *)
              (state\<lparr>state_dr_val := (state_dr_val state)
                (sp := ((state_dr_val state) sp)
                  (p := Some (val_rlist (mk_list vv (length vl)))))\<rparr>)
          )
          |_ \<Rightarrow> (* sp is not a vector, just assign e to sp. *)
            (state\<lparr>state_dr_val := (state_dr_val state)
              (sp := ((state_dr_val state) sp)(p := state_val_exp_t e state))\<rparr>)
       )
      |None \<Rightarrow> state (* This case should not happen. See the NOTEs vhdl_syntax.thy. *)
      )
    )
    |clhs_sp (lhs_sa sp r) \<Rightarrow> (
      case rhs of 
       rhs_e e \<Rightarrow> (
        case state_val_exp_t e state of Some (val_list vl) \<Rightarrow> (
          case (state_sp state) sp of 
            Some (val_list sp_vl) \<Rightarrow> (
              case r of vhdl_dis_to e1 e2 \<Rightarrow>
                 let i = nat_of_val_op (state_val_exp_t e1 state);
                     j = nat_of_val_op (state_val_exp_t e2 state) in
                 (state\<lparr>state_dr_val := (state_dr_val state)
                   (sp := ((state_dr_val state) sp)
                     (p := Some (val_list (assign_range_to sp_vl i j vl))))\<rparr>) 
              |_ \<Rightarrow> state (* We currently restricts that the endianness of the LHS and the RHS must be consistent. *)
          )  
          |_ \<Rightarrow> (state\<lparr>state_dr_val := (state_dr_val state)
                  (sp := ((state_dr_val state) sp)(p := None))\<rparr>)
        )
        |Some (val_rlist vl) \<Rightarrow> (
          case (state_sp state) sp of 
            Some (val_rlist sp_vl) \<Rightarrow> (
              case r of vhdl_dis_downto e1 e2 \<Rightarrow>
                let i = nat_of_val_op (state_val_exp_t e1 state);
                    j = nat_of_val_op (state_val_exp_t e2 state) in
                (state\<lparr>state_dr_val := (state_dr_val state)
                  (sp := ((state_dr_val state) sp)
                    (p := Some (val_rlist (assign_range_downto sp_vl i j vl))))\<rparr>)
              |_ \<Rightarrow> state (* We currently restricts that the endianness of the LHS and the RHS must be consistent. *)
          )  
          |_ \<Rightarrow> (state\<lparr>state_dr_val := (state_dr_val state)
                  (sp := ((state_dr_val state) sp)(p := None))\<rparr>)
        )
        |_ \<Rightarrow> (state\<lparr>state_dr_val := (state_dr_val state)
               (sp := ((state_dr_val state) sp)(p := None))\<rparr>)
      )
      |rhs_o e \<Rightarrow> (
        case state_val_exp_t e state of None \<Rightarrow>
          (state\<lparr>state_dr_val := (state_dr_val state)
            (sp := ((state_dr_val state) sp)(p := None))\<rparr>)
        |Some vv \<Rightarrow> (
          case (state_sp state) sp of 
           Some (val_list sp_vl) \<Rightarrow> (
            case r of (* We require that TO can only be used with val_list. *)
             vhdl_dis_to e1 e2 \<Rightarrow>
              let i = nat_of_val_op (state_val_exp_t e1 state);
                  j = nat_of_val_op (state_val_exp_t e2 state) in
              (state\<lparr>state_dr_val := (state_dr_val state)
                (sp := ((state_dr_val state) sp)
                  (p := Some (val_list (assign_range_to sp_vl i j (mk_list vv (j-i+1))))))\<rparr>)
          )
          |Some (val_rlist sp_vl) \<Rightarrow> (
            case r of (* We require that DOWNTO can only be used with val_rlist. *)
             vhdl_dis_downto e1 e2 \<Rightarrow>
              let i = nat_of_val_op (state_val_exp_t e1 state);
                  j = nat_of_val_op (state_val_exp_t e2 state) in
              (state\<lparr>state_dr_val := (state_dr_val state)
                (sp := ((state_dr_val state) sp)
                  (p := Some (val_rlist (assign_range_downto sp_vl i j (mk_list vv (i-j+1))))))\<rparr>)
          )
          |_ \<Rightarrow> (state\<lparr>state_dr_val := (state_dr_val state)
                 (sp := ((state_dr_val state) sp)(p := None))\<rparr>)
        )
      )
    )
  )
  |_ \<Rightarrow> state"

text {* A variable assignment statement only changes the current value of the
variable. Variables don't have drivers. *}

text {* Variable assignment. 
Here we DON'T deal with assignment of records, i.e., clhs_vr := crhs_r rhsl. 
Assignment of records is translated to assignment of members in the record. *}

definition exec_var_asmt:: "seq_stmt \<Rightarrow> vhdl_state \<Rightarrow> vhdl_state"  where
"exec_var_asmt ss state \<equiv>
  case ss of (sst_va n lhs rhs) \<Rightarrow> (
    case lhs of clhs_v (lhs_v v) \<Rightarrow> (
      case rhs of
       rhs_e e \<Rightarrow> (state\<lparr>state_var := (state_var state)(v := state_val_exp_t e state)\<rparr>)
      |rhs_o e \<Rightarrow> (  
        case var_init_val v of
         Some (val_list vl) \<Rightarrow> (
          case state_val_exp_t e state of None \<Rightarrow> (* e doesn't have a valid value. *)
            (state\<lparr>state_var := (state_var state)(v := None)\<rparr>)
          |Some vv \<Rightarrow> (* e has a valid value vv. *)
            (state\<lparr>state_var := (state_var state)
              (v := Some (val_list (mk_list vv (length vl))))\<rparr>)
        )
        |Some (val_rlist vl) \<Rightarrow> (
          case state_val_exp_t e state of None \<Rightarrow> (* e doesn't have a valid value. *)
            state\<lparr>state_var := (state_var state)(v := None)\<rparr>
          |Some vv \<Rightarrow> (* e has a valid value vv. *)
            (state\<lparr>state_var := (state_var state)
              (v := Some (val_rlist (mk_list vv (length vl))))\<rparr>)
        )
        |_ \<Rightarrow> (* v is not a vector, just assign e to v. *)
          (state\<lparr>state_var := (state_var state)(v := state_val_exp_t e state)\<rparr>)
      )
    )
    |clhs_v (lhs_va v r) \<Rightarrow> (
      case rhs of 
       rhs_e e \<Rightarrow> (
        case state_val_exp_t e state of Some (val_list vl) \<Rightarrow> (
          case (state_var state) v of 
            Some (val_list v_vl) \<Rightarrow> (
              case r of vhdl_dis_to e1 e2 \<Rightarrow>
                 let i = nat_of_val_op (state_val_exp_t e1 state);
                     j = nat_of_val_op (state_val_exp_t e2 state) in
                 (state\<lparr>state_var := (state_var state)
                  (v := Some (val_list (assign_range_to v_vl i j vl)))\<rparr>) 
               |_ \<Rightarrow> state (* We currently restricts that the endianness of the LHS and the RHS must be consistent. *)
          )  
          |_ \<Rightarrow> (state\<lparr>state_var := (state_var state)(v := None)\<rparr>)
        )
        |Some (val_rlist vl) \<Rightarrow> (
          case (state_var state) v of 
            Some (val_rlist v_vl) \<Rightarrow> (
              case r of vhdl_dis_downto e1 e2 \<Rightarrow>
                let i = nat_of_val_op (state_val_exp_t e1 state);
                    j = nat_of_val_op (state_val_exp_t e2 state) in
                (state\<lparr>state_var := (state_var state)
                  (v := Some (val_rlist (assign_range_downto v_vl i j vl)))\<rparr>)
              |_ \<Rightarrow> state (* We currently restricts that the endianness of the LHS and the RHS must be consistent. *)
          )  
          |_ \<Rightarrow> (state\<lparr>state_var := (state_var state)(v := None)\<rparr>)
        )
        |_ \<Rightarrow> (state\<lparr>state_var := (state_var state)(v := None)\<rparr>)
      )
      |rhs_o e \<Rightarrow> (
        case state_val_exp_t e state of None \<Rightarrow>
          state\<lparr>state_var := (state_var state)(v := None)\<rparr>
        |Some vv \<Rightarrow> (
          case (state_var state) v of 
           Some (val_list v_vl) \<Rightarrow> (
            case r of vhdl_dis_to e1 e2 \<Rightarrow> (* We require that TO can only be used with val_list. *)
              let i = nat_of_val_op (state_val_exp_t e1 state);
                  j = nat_of_val_op (state_val_exp_t e2 state) in
              (state\<lparr>state_var := (state_var state)
                (v := Some (val_list (assign_range_to v_vl i j (mk_list vv (j-i+1)))))\<rparr>)
          )
          |Some (val_rlist v_vl) \<Rightarrow> (
            case r of vhdl_dis_downto e1 e2 \<Rightarrow> (* We require that DOWNTO can only be used with val_rlist. *)
              let i = nat_of_val_op (state_val_exp_t e1 state);
                  j = nat_of_val_op (state_val_exp_t e2 state) in
              (state\<lparr>state_var := (state_var state)
                (v := Some (val_rlist (assign_range_downto v_vl i j (mk_list vv (i-j+1)))))\<rparr>)
          )
          |_ \<Rightarrow> (state\<lparr>state_var := (state_var state)(v := None)\<rparr>)
        )
      )
    )
  )
  |_ \<Rightarrow> state"

text {* Translate the ssc_sal statement, i.e., record assignment of signals/ports. *}

fun trans_sal:: "name \<Rightarrow> spl \<Rightarrow> rhsl \<Rightarrow> seq_stmt list" where
"trans_sal n (spl_s s1) (rl_s s2) = [(sst_sa n (clhs_sp (lhs_s (sp_s s1))) (rhs_e (exp_sig s2)))]" 
|"trans_sal n (spl_s s1) (rl_p p2) = [(sst_sa n (clhs_sp (lhs_s (sp_s s1))) (rhs_e (exp_prt p2)))]" 
|"trans_sal n (spl_s s1) (rl_v v2) = [(sst_sa n (clhs_sp (lhs_s (sp_s s1))) (rhs_e (exp_var v2)))]" 
|"trans_sal n (spl_p p1) (rl_s s2) = [(sst_sa n (clhs_sp (lhs_s (sp_p p1))) (rhs_e (exp_sig s2)))]" 
|"trans_sal n (spl_p p1) (rl_p p2) = [(sst_sa n (clhs_sp (lhs_s (sp_p p1))) (rhs_e (exp_prt p2)))]" 
|"trans_sal n (spl_p p1) (rl_v v2) = [(sst_sa n (clhs_sp (lhs_s (sp_p p1))) (rhs_e (exp_var v2)))]"
|"trans_sal n (spnl nl1) (rnl []) = []"
|"trans_sal n (spnl nl1) (rnl (y#ys)) = (
  case nl1 of (n,[]) \<Rightarrow> []
  |(n,(x#xs)) \<Rightarrow> (trans_sal n x y)@(trans_sal n (spnl (n,xs)) (rnl ys))
)"
(* The following means the record types don't match. *)
|"trans_sal n (spl_s s) (rnl l) = []"
|"trans_sal n (spl_p p) (rnl l) = []"
|"trans_sal n (spnl nl1) (rl_s s) = []"
|"trans_sal n (spnl nl1) (rl_p p) = []"
|"trans_sal n (spnl nl1) (rl_v v) = []"

text {* Translate the ssc_val statement, i.e., record assignment of variables. *}

fun trans_val:: "name \<Rightarrow> vl \<Rightarrow> rhsl \<Rightarrow> seq_stmt list" where
"trans_val n (vl_v v1) (rl_s s2) = [(sst_va n (clhs_v (lhs_v v1)) (rhs_e (exp_sig s2)))]"
|"trans_val n (vl_v v1) (rl_p p2) = [(sst_va n (clhs_v (lhs_v v1)) (rhs_e (exp_prt p2)))]"
|"trans_val n (vl_v v1) (rl_v v2) = [(sst_va n (clhs_v (lhs_v v1)) (rhs_e (exp_var v2)))]"
|"trans_val n (vnl nl1) (rnl []) = []"
|"trans_val n (vnl nl1) (rnl (y#ys)) = (
  case nl1 of (n,[]) \<Rightarrow> []
  |(n,(x#xs)) \<Rightarrow> (trans_val n x y)@(trans_val n (vnl (n,xs)) (rnl ys))
)"
(* The following means that record types don't match. *)
|"trans_val n (vl_v v) (rnl l) = []"
|"trans_val n (vnl l) (rl_s s) = []"
|"trans_val n (vnl l) (rl_p p) = []"
|"trans_val n (vnl l) (rl_v v) = []"

text {* The execution of the next statement changes the next flag (string, bool)
where string is the name of the loop, bool is the flag. *}

definition exec_next_stmt:: "seq_stmt \<Rightarrow> vhdl_state \<Rightarrow> vhdl_state" where
"exec_next_stmt ss state \<equiv> 
  case ss of (sst_n n1 n2 c) \<Rightarrow> (
    case state_val_exp_t c state of 
    Some (val_b b) \<Rightarrow> state\<lparr>next_flag := (n2, b)\<rparr>
    |_ \<Rightarrow> state)
  |_ \<Rightarrow> state"

text {* The execution of the exit statement changes the next flag (string, bool)
where string is the name of the loop, bool is the flag. *}

definition exec_exit_stmt:: "seq_stmt \<Rightarrow> vhdl_state \<Rightarrow> vhdl_state" where
"exec_exit_stmt ss state \<equiv> 
  case ss of (sst_e n1 n2 c) \<Rightarrow> (
    case state_val_exp_t c state of 
    Some (val_b b) \<Rightarrow> state\<lparr>exit_flag := (n2, b)\<rparr>
    |_ \<Rightarrow> state)
  |_ \<Rightarrow> state"

text {* Get the subprogram from the subprogram call. *}

primrec get_subprog:: "subprogcall \<Rightarrow> subprogram list \<Rightarrow> subprogram option" where
"get_subprog spc [] = None"
|"get_subprog spc (p#px) = (if (fst spc) = (fst p) then Some p else get_subprog spc px)"

text {* Generate a list of variable assignment statements for passing 
parameters into/outta a function call. *}

primrec pass_in_para_gen:: "parameter_list \<Rightarrow> v_clhs list \<Rightarrow> seq_stmt list" where
"pass_in_para_gen [] l2 = []"
|"pass_in_para_gen (p#px) l2 = (
  if (fst (snd p)) \<in> {dir_in, dir_inout} then
    (sst_va '''' (fst p) (asmt_rhs_of_v_clhs (hd l2)))#(pass_in_para_gen px (tl l2))
  else (pass_in_para_gen px (tl l2))
)"

primrec pass_out_para_gen:: "parameter_list \<Rightarrow> v_clhs list \<Rightarrow> seq_stmt list" where
"pass_out_para_gen [] l2 = []"
|"pass_out_para_gen (p#px) l2 = (
  if (fst (snd p)) \<in> {dir_out, dir_inout} then
    (sst_va '''' (hd l2) (asmt_rhs_of_v_clhs (fst p)))#(pass_out_para_gen px (tl l2))
  else (pass_out_para_gen px (tl l2))
)"

text {* Restore the values of local variables after a subprogram call. 
This is only necessary when there are recursive subprogram calls. 
The first state is the state before the subprogram call, 
the second state is the state after the subprogram call.
Return a new state in which the values of local variables are restored. *}

definition restore_local_v_lhs:: "v_lhs \<Rightarrow> vhdl_state \<Rightarrow> vhdl_state \<Rightarrow> vhdl_state" where
"restore_local_v_lhs v s1 s2 \<equiv> case v of 
  lhs_v v \<Rightarrow> (s2\<lparr>state_var := (state_var s2)(v := state_val_exp_t (exp_var v) s1)\<rparr>)
  |lhs_va v r \<Rightarrow> (s2\<lparr>state_var := (state_var s2)(v := state_val_exp_t (exp_var v) s1)\<rparr>)
"

fun restore_local_vl:: "vl list \<Rightarrow> vhdl_state \<Rightarrow> vhdl_state \<Rightarrow> vhdl_state" where
"restore_local_vl [] s1 s2 = s2"
|"restore_local_vl (v#vx) s1 s2 = (case v of
  vl_v v \<Rightarrow> (s2\<lparr>state_var := (state_var s2)(v := state_val_exp_t (exp_var v) s1)\<rparr>)
 |vnl (n,vll) \<Rightarrow> restore_local_vl vll s1 s2
)"

fun restore_local_var:: "local_var_list \<Rightarrow> vhdl_state \<Rightarrow> vhdl_state \<Rightarrow> vhdl_state" where
"restore_local_var [] s1 s2 = s2"
|"restore_local_var (v#vx) s1 s2 = (case v of
  clhs_v v \<Rightarrow> restore_local_v_lhs v s1 s2
  |clhs_vr vr \<Rightarrow> restore_local_vl [vr] s1 s2
)"

text {* exec_seq_stmt gives the operational semantics for the following sequential
statements: if statement, loop statement, next statement, and exit statement. 
the seq_stmt list belongs to the process_stmt. 
The first (string, bool) is the flag for next, where string gives the loop name
and bool is the flag. The second (string, bool) is the flag for exit, where
string gives the loop name and the bool is the flag. 
This function may not be terminating. 

This function returns (state, return crhs). The latter is only used 
in functions. For other statements, we simply return a null crhs *}

definition null_rhs:: "asmt_rhs" where "null_rhs \<equiv> rhs_e (exp_con (vhdl_integer,(val_i 0)))"

function exec_seq_stmt_list:: "conc_stmt \<Rightarrow> seq_stmt list \<Rightarrow> subprogram list \<Rightarrow> vhdl_state \<Rightarrow> (vhdl_state \<times> asmt_rhs)" 
and exec_if_stmt:: "conc_stmt \<Rightarrow> seq_stmt \<Rightarrow> subprogram list \<Rightarrow> vhdl_state \<Rightarrow> (vhdl_state \<times> asmt_rhs)" 
and exec_loop_stmt:: "conc_stmt \<Rightarrow> seq_stmt \<Rightarrow> subprogram list \<Rightarrow> vhdl_state \<Rightarrow> (vhdl_state \<times> asmt_rhs)" 
and rec_loop:: "conc_stmt \<Rightarrow> seq_stmt \<Rightarrow> subprogram list \<Rightarrow> vhdl_state \<Rightarrow> (vhdl_state \<times> asmt_rhs)" where
"exec_seq_stmt_list p [] subps state = (state,null_rhs)"
|"exec_seq_stmt_list p (s#sx) subps state = (
  if (snd (next_flag state)) \<or> (snd (exit_flag state)) 
  then (state,null_rhs) (* If next or exit flag is true, the current 
  statement is skipped. *)
  else
    case s of 
    sst_sa n sp e \<Rightarrow> (case (sp,e) of 
       ((clhs_spr lhs),(rhs_e (exp_r rhs))) \<Rightarrow> exec_seq_stmt_list p ((trans_sal n lhs rhs)@sx) subps state
      |((clhs_sp lhs),_) \<Rightarrow> exec_seq_stmt_list p sx subps (exec_sig_asmt p s state)
    )
      (*|_ \<Rightarrow> exec_seq_stmt_list p sx subps state) (* Can't assign record type to non-record type nor vice versa. *)*)
    |sst_va n v e \<Rightarrow> (case (v,e) of 
       ((clhs_vr lhs),(rhs_e (exp_r rhs))) \<Rightarrow> exec_seq_stmt_list p ((trans_val n lhs rhs)@sx) subps state
      |((clhs_v lhs),_) \<Rightarrow> exec_seq_stmt_list p sx subps (exec_var_asmt s state)
      (*|_ \<Rightarrow> exec_seq_stmt_list p sx subps state) (* Can't assign record type to non-record type nor vice versa. *)*)
    )
    |sst_if n c sl1 sl2 \<Rightarrow> exec_seq_stmt_list p sx subps (fst (exec_if_stmt p s subps state))
    |sst_l n c sl \<Rightarrow> exec_seq_stmt_list p sx subps (fst (exec_loop_stmt p s subps state))
    |sst_fn n v spc \<Rightarrow> (
      case get_subprog spc subps of None \<Rightarrow> (state,null_rhs) (* This function is not defined. *)
      |Some prog \<Rightarrow> (
        let para_in_stmts = pass_in_para_gen (fst (snd (snd prog))) (fst (snd spc));
            (n_state,result) = exec_seq_stmt_list p (para_in_stmts@(fst (snd (snd (snd prog))))) subps state;
            para_out_stmt = [(sst_va '''' v result)];
            f_state = restore_local_var (snd (snd (snd (snd (snd prog))))) state n_state
        in
        exec_seq_stmt_list p (para_out_stmt@sx) subps f_state
      )
    ) 
    |sst_rt n e \<Rightarrow> (state,e)
    |sst_pc n spc \<Rightarrow> (
      case get_subprog spc subps of None \<Rightarrow> (state,null_rhs) (* This function is not defined. *)
      |Some prog \<Rightarrow> (
        let para_in_stmts = pass_in_para_gen (fst (snd (snd prog))) (fst (snd spc));
            (n_state,result) = exec_seq_stmt_list p (para_in_stmts@(fst (snd (snd (snd prog))))) subps state;
            para_out_stmts = pass_out_para_gen (fst (snd (snd prog))) (fst (snd spc));
            f_state = restore_local_var (snd (snd (snd (snd (snd prog))))) state n_state
        in
        exec_seq_stmt_list p (para_out_stmts@sx) subps f_state
      )
    )
    |sst_n n1 n2 c \<Rightarrow> 
      let n_state = (exec_next_stmt s state) in
      if snd (next_flag n_state) then (n_state,null_rhs) (* If the next flag is true, 
      ignore the reminder of the sequential statements. *)
      else exec_seq_stmt_list p sx subps n_state (* N.B. In this case, n_state = state. *)
    |sst_e n1 n2 c \<Rightarrow> 
      let n_state = (exec_exit_stmt s state) in
      if snd (exit_flag n_state) then (n_state,null_rhs) (* If the exit flag is true, 
      ignore the reminder of the sequential statements. *)
      else exec_seq_stmt_list p sx subps n_state (* N.B. In this case, n_state = state. *)
    |sst_nl \<Rightarrow> exec_seq_stmt_list p sx subps state)"
|"exec_if_stmt p s subps state = (
  case s of (sst_if n c ssl1 ssl2) \<Rightarrow> (
    case state_val_exp_t c state of 
    Some (val_b True) \<Rightarrow> (* Execute the 'then' part. *)
      exec_seq_stmt_list p ssl1 subps state
    |_ \<Rightarrow> (* Execute the 'else' part. *) 
      exec_seq_stmt_list p ssl2 subps state))"
|"exec_loop_stmt p s subps state = (
  case s of (sst_l n c ssl) \<Rightarrow> (
    if snd (exit_flag state) \<and> (fst (exit_flag state) = n) then (* Exit this loop. *)
      ((state\<lparr>exit_flag := ('''', False)\<rparr>),null_rhs) (* Reset the exit flag. *)
    else if snd (exit_flag state) then 
    (* Need to exit an outer loop. Exit this loop. *)
      (state,null_rhs)
    else if snd (next_flag state) \<and> (fst (next_flag state) = n) then 
    (* Continue this loop, but reset the next flag. *)
      rec_loop p s subps (state\<lparr>next_flag := ('''', False)\<rparr>)
    else if snd (next_flag state) then
    (* The next statement is effective for an outer loop. Exit this loop. *)
      (state,null_rhs)
    else (* Execute this loop. *)
      rec_loop p s subps state))"
|"rec_loop p s subps state = (
  case s of (sst_l n c ssl) \<Rightarrow> (
    case state_val_exp_t c state of 
    Some (val_b True) \<Rightarrow> (* Execute the loop once, then do recursion. *)
      exec_loop_stmt p s subps (fst (exec_seq_stmt_list p ssl subps state))
    |_ \<Rightarrow> (state,null_rhs)))" (* Exit the loop. *) 
by pat_completeness auto
termination sorry

primrec get_drivers_sub:: "sigprt \<Rightarrow> conc_stmt_list \<Rightarrow> vhdl_state \<Rightarrow> val list" where
"get_drivers_sub sp [] state = []"
|"get_drivers_sub sp (c#cs) state = (
  case c of cst_ps n sensl ssl \<Rightarrow> 
    let this_val = (state_dr_val state) sp c in (
    case this_val of None \<Rightarrow> get_drivers_sub sp cs state
    |Some v \<Rightarrow> (v#(get_drivers_sub sp cs state))))"

definition get_drivers:: "sigprt \<Rightarrow> vhdl_desc \<Rightarrow> vhdl_state \<Rightarrow> val list" where
"get_drivers sp desc state \<equiv> get_drivers_sub sp (fst (snd (snd desc))) state"

text {* We compute the effective value of a signal/port based on its driving values. 
Therefore we assume the following function is only involved when the current simulation
cycle is already executed and all the driving values are computed. 
Here we use a simplified version where we assume each signal is driven by a single process,
becuase (1) LEON3 design seems to assume so, and (2) " this is not a real restriction. 
One may everywhere replace references to resolved signals by the appropriate expression 
in the contributing output signals." [Page 48, formal semantics for VHDL].
***** N.B. We'd like to preserve the commented code, which is more general and 
could be useful for future development. *}

definition get_eff_val:: "sigprt \<Rightarrow> vhdl_desc \<Rightarrow> vhdl_state \<Rightarrow> val option" where
"get_eff_val sp desc state \<equiv> 
  let drivers = get_drivers sp desc state in
  if drivers = [] then (* This signal/port has no drivers, 
  thus its value is always the initial value, which must be its current value. *)
    (state_sp state) sp
  else (* We assume each signal/port only has 1 driver,
  no resolution is needed. *)
    Some (hd drivers)
"

(* A more general implementation of get_eff_val considering multiple drivers
 * for signals/ports. 
definition get_eff_val:: "sigprt \<Rightarrow> vhdl_desc \<Rightarrow> vhdl_state \<Rightarrow> val option" where
"get_eff_val sp desc state \<equiv> 
  let drivers = get_drivers sp desc state in
  if drivers = [] then (* This signal/port has no drivers, 
  thus its value is always the initial value, which must be its current value. *)
    (state_sp state) sp
  else if List.length drivers = 1 then (* This signal/port has only 1 driver,
  no resolution is needed. *)
    Some (hd drivers)
  else (* This signal/port has multiple drivers. *)
    case (fst (snd desc)) sp of Some rf \<Rightarrow> (* This signal/port has a resolution function. *)
      Some (rf (get_drivers sp desc state))
    |None \<Rightarrow> None (* This signal/port has multiple drivers and it's an unresolved signal. *)
"
*)

text {* Check if the signal/port's value is changed during the last execution
of processes in the current simulation. Return the list of active signals/ports,
i.e., those that are changed.
N.B. Processes may be executed multiple times in one simulation cycle. *}

primrec get_active_sigprt:: "sigprt list \<Rightarrow> vhdl_state \<Rightarrow> sigprt list" where
"get_active_sigprt [] state = []"
|"get_active_sigprt (s#sx) state = (
  if (state_sp state s) = (state_eff_val state s) then get_active_sigprt sx state
  else [s]@(get_active_sigprt sx state))" 

definition active_sigprts:: "vhdl_desc \<Rightarrow> vhdl_state \<Rightarrow> sigprt list" where
"active_sigprts desc state \<equiv> get_active_sigprt (env_sp (fst desc)) state"

text {* Given a list of active signals/ports, check if a sensitivity_list 
contains active signals/ports. *}

primrec has_active_sigprt:: "sensitivity_list \<Rightarrow> sigprt list \<Rightarrow> bool" where
"has_active_sigprt [] sl = False"
|"has_active_sigprt (s#sx) sl = (
  if List.member sl s then True 
  else has_active_sigprt sx sl)"

primrec find_active_process:: "conc_stmt_list \<Rightarrow> sigprt list \<Rightarrow> bool" where
"find_active_process [] sl = False"
|"find_active_process (c#cs) sl = (
  case c of cst_ps n sensl ssl \<Rightarrow>
    if has_active_sigprt sensl sl then True
    else find_active_process cs sl)"

definition has_active_processes:: "vhdl_desc \<Rightarrow> sigprt list \<Rightarrow> bool" where
"has_active_processes desc sl \<equiv> find_active_process (fst (snd (snd desc))) sl"

text {* Execute all the process statements in a sequential order.
There are many previous studies that make assumptions so that the order
of execution of concurrent processes does not matter. For example,
the ACL2 work assumes: 
"each process only writes in its local variables and in the new values of its signal drivers, 
the order in which concurrent processes are called and transmit the dynamic state to 
each other has no influence on the result" 
[Formal verification of VHDL using VHDL-like ACL2 models,
Borrione and Georgelin].
Here we adopt the same assumption.
A process is only executed when its sensitivity list has an active
signal/port. *}

primrec exec_proc_all:: "conc_stmt_list \<Rightarrow> sigprt list \<Rightarrow> subprogram list \<Rightarrow> vhdl_state \<Rightarrow> vhdl_state" where
"exec_proc_all [] sl subps state = state"
|"exec_proc_all (c#cs) sl subps state = (
  case c of cst_ps n sensl ssl \<Rightarrow> 
      if has_active_sigprt sensl sl then
        exec_proc_all cs sl subps (fst (exec_seq_stmt_list c ssl subps state))
      else exec_proc_all cs sl subps state)"

text {* Compute the effective value of signals/ports. *}

primrec comp_eff_val:: "sigprt list \<Rightarrow> vhdl_desc \<Rightarrow> vhdl_state \<Rightarrow> vhdl_state" where
"comp_eff_val [] desc state = state"
|"comp_eff_val (s#sx) desc state = (
  let n_state = state\<lparr>state_eff_val := (state_eff_val state)(s := (get_eff_val s desc state))\<rparr> in
  comp_eff_val sx desc n_state)"

text {* Copy the signals/ports' effective value to their current value. *}

primrec update_sigprt:: "sigprt list \<Rightarrow> vhdl_state \<Rightarrow> vhdl_state" where
"update_sigprt [] state = state"
|"update_sigprt (s#sx) state = (
  let n_state = state\<lparr>state_sp := (state_sp state)(s := (state_eff_val state s))\<rparr> in
  update_sigprt sx n_state)"

text {* In a simulation cycle, we execute all the process once each, 
then update the signal/port current values. 
If a process's sensitivity list has an active signal/port, that 
process is resumed and executed again.
This procedure ends when all processes' sensitivity lists don't have 
any active signals/ports. 
This function may not be terminating. *}

function resume_processes:: "vhdl_desc \<Rightarrow> sigprt list \<Rightarrow> vhdl_state \<Rightarrow> vhdl_state" where
"resume_processes desc spl state = (
  let state1 = exec_proc_all (fst (snd (snd desc))) spl (snd (snd (snd desc))) state;
      state2 = comp_eff_val (env_sp (fst desc)) desc state1;
      act_sp1 = active_sigprts desc state2; 
      state3 = update_sigprt (env_sp (fst desc)) state2 in
      if has_active_processes desc act_sp1 then 
        resume_processes desc act_sp1 state3
      else state3)"
by pat_completeness auto
termination sorry

definition exec_sim_cyc:: "vhdl_desc \<Rightarrow> vhdl_state \<Rightarrow> vhdl_state" where
"exec_sim_cyc desc state \<equiv> 
  let act_sp = active_sigprts desc state in
  if has_active_processes desc act_sp then 
    resume_processes desc act_sp state
  else state"

definition emp_state:: "vhdl_state" where
"emp_state \<equiv> \<lparr>state_sp = \<lambda>x.(None), state_var = \<lambda>x.(None), 
  state_eff_val = \<lambda>x.(None), state_dr_val = \<lambda>x y.(None), 
  next_flag = ('''', False), exit_flag = ('''', False)\<rparr>"

definition init_sp:: "sigprt \<Rightarrow> val option" where
"init_sp sp \<equiv> 
  case sp of sp_s s \<Rightarrow> (
    case init_val_exp_t (snd (snd (snd s))) of
    Some v \<Rightarrow>
      if v = val_null then None
      else Some v
    |None \<Rightarrow> None
  )
  | sp_p p \<Rightarrow> (
    case init_val_exp_t (snd (snd (snd (snd p)))) of 
    Some v \<Rightarrow> 
      if v = val_null then None
      else Some v
    | None \<Rightarrow> None)"
                       
definition init_var:: "variable \<Rightarrow> val option" where
"init_var v \<equiv> 
  case init_val_exp_t (snd (snd v)) of
   Some v \<Rightarrow> 
    if v = val_null then None else Some v
  |None \<Rightarrow> None"

text {* In the initial state, the values of signals, ports, and variables
are their initial values. 
We assume there is a port clk of type vhdl_bit for the master clock.
We assume the initial value of clk is '0'. *}

definition p_clk:: "port" where
"p_clk \<equiv> (''clk'', vhdl_std_ulogic, mode_in, connected, 
  (exp_con (vhdl_std_ulogic, (val_c (CHR ''0'')))))"

definition init_state:: "vhdl_state" where
"init_state \<equiv>
  let state1 = emp_state\<lparr>state_sp := init_sp\<rparr>\<lparr>state_var := init_var\<rparr> in
  state1\<lparr>state_sp := (state_sp state1)((sp_p p_clk) := Some (val_c (CHR ''0'')))\<rparr>"

text {* The function below models the simulation of n cycles. 
We assume there is a signal clk of type vhdl_bit in the state for the master clock.
The value of clk flips in every simulation cycle. *}

definition flip_clk:: "vhdl_state \<Rightarrow> vhdl_state" where
"flip_clk state \<equiv> 
  let this_clk = state_sp state (sp_p p_clk) in 
  if this_clk = Some (val_c (CHR ''0'')) then
    state\<lparr>state_sp := (state_sp state)((sp_p p_clk) := Some (val_c (CHR ''1'')))\<rparr>
  else state\<lparr>state_sp := (state_sp state)((sp_p p_clk) := Some (val_c (CHR ''0'')))\<rparr>"

fun exec_sim:: "nat \<Rightarrow> vhdl_desc \<Rightarrow> vhdl_state \<Rightarrow> vhdl_state" where
"exec_sim 0 desc state = state"
|"exec_sim n desc state = exec_sim (n-1) desc (flip_clk (exec_sim_cyc desc state))"

text {* Since we only use sensitivity list for processes, for each process,
"All sequential statements will execute once at simulation startup
in such processes and after that the processes will suspend." 
In this startup execution, we simply say all the signals are active,
thus every process will be executed. *}

definition simulation:: "nat \<Rightarrow> vhdl_desc \<Rightarrow> vhdl_state \<Rightarrow> vhdl_state" where
"simulation n desc state \<equiv> 
  exec_sim n desc (resume_processes desc (env_sp (fst desc)) state)"

end