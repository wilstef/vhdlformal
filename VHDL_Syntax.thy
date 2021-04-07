(*
 * Copyright 2016, NTU
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * Author: Zhe Hou.
 *)

theory VHDL_Syntax
  imports Main HOL.Real
begin

text {* This file defines the core syntax of the VHDL model.
The following syntax is based on Chapter 3 - 6 of [1].
[1] "Formal Semantics and Proof Techniques for Optimising VHDL Models"
I'll capitalise the initials for datatype and type_synonum names.
Names for definitions are not capitalised.  *}

type_synonym name = string

text {* val gives the primary data type values in VHDL. User defined types should 
have values based on these. *}

datatype val = 
  val_i int
| val_r real
| val_c char
| val_b bool
| val_null
| val_list "val list" (* Normal list, for "to". *)
| val_rlist "val list" (* Reversed list, for "downto". *)

text {* type = (name, parent-type, val list). where parent-type denotes the parent 
type for a given subtype (parent-type = emptype if not a subtype).  
val list gives all the valid values of the type. *}

datatype type = 
  emptype 
| subtype name type 

datatype signal_kind = register | bus | discrete

datatype shared_status = shared | not_shared

datatype mode = mode_in | mode_out | mode_inout | mode_buffer | mode_linkage

datatype connection = connected | unconnected

text {* Unary operators. *}

datatype uop =
uop_abs ("[abs]")
|uop_not ("[not]")
|uop_neg ("[-:]")
|uop_pos ("[+:]")

text {* Logical operators. *}

datatype lop =
lop_and ("[and]")
|lop_or ("[or]")
|lop_nand ("[nand]")
|lop_nor ("[nor]")
|lop_xor ("[xor]")
|lop_xnor ("[xnor]")

text {* Relational operators. *}

datatype rop =
rop_eq ("[=]")
|rop_neq ("['/=]")
|rop_lt ("[<]")
|rop_leq ("[<=]")
|rop_gt ("[>]")
|rop_geq ("[>=]")

text {* Shift operators. *}

datatype sop = 
sop_sll ("[sll]")
|sop_srl ("[srl]")
|sop_sla ("[sla]")
|sop_sra ("[sra]")
|sop_rol ("[rol]")
|sop_ror ("[ror]")

text {* Arithmetic operators: 
Adding operators, multiplying operators, concatenation, and exponentiation. *}

datatype aop =
aop_add ("[+]")
|aop_sub ("[-]")
|aop_con ("[&]")
|aop_mul ("[*]")
|aop_div ("['/]")
|aop_mod ("[mod]")
|aop_rem ("[rem]")
|aop_exp ("[**]")

type_synonym const = "(type \<times> val)"

datatype expression =
uexp uop expression 
|bexpl expression lop expression 
|bexpr expression rop expression 
|bexps expression sop expression 
|bexpa expression aop expression 
|exp_sig "(name \<times> type \<times> signal_kind \<times> expression)"               
|exp_prt "(name \<times> type \<times> mode \<times> connection \<times> expression)"
|exp_var "(name \<times> type \<times> expression)"
|exp_con const
|exp_nth expression expression (* Get the nth member of a list. 
The first expression is the list, the second expression is the index (natural number)*)
|exp_sl expression expression expression 
(* Get a sublist of a list. The first expression is a list, 
the last two expressions are the indices (natural numbers). 
We insist that the value of the second expression is less than or equal to
the value of the last expression. *)
|exp_tl expression 
(* This construct converts the type of expression to an array/vector/list type. 
That is, VHDL code often uses 
v1 + v2 or v1 & v2 
where, e.g., v1 is std_logic_vector and v2 is std_logic.
To handle this, we explicitly convert v2 to a vector with 1 member. 
So in our model, we write, e.g.,
(exp_var v1) + (exp_tl (exp_var v2)).
*)
|exp_trl expression
(* Same as above, but converts the type of expression to a reversed 
list type (for DOWNTO). *)
|exp_fc "(name \<times> (expression list) \<times> type)" 
(* Although we define exp_fc, the core model does not support functions as 
expression. Functions are supported in the complex model in the form of statements. 
That is, we will translate functions in expressions to statements as below: 
v1 := f(n) + v2;
will be translated to
t := f(n);
v1 := t + v2;
where t is a temporary variable (of type). Thus we only need to support 
"function statements" of the form
variable := function(args...);
And we can evaluate functions when executing sequential statements.
*)
|exp_r rhsl
and rhsl = 
rl_s "(name \<times> type \<times> signal_kind \<times> expression)"
|rl_p "(name \<times> type \<times> mode \<times> connection \<times> expression)"
|rl_v "(name \<times> type \<times> expression)"
|rnl "rhsl list"

text {* signal = (name, type, signal-kind, initial-expression). *}

type_synonym signal = "(name \<times> type \<times> signal_kind \<times> expression)"

text {* port ( name, type, mode, connection, defualt-expression). *}

type_synonym port = "(name \<times> type \<times> mode \<times> connection \<times> expression)"

text {* variable = (name, type, initial-expression ). 
For determinism, we don't consider shared variables. 
LEON3 design doesn't use shared variables. Thus all variables are 
local to the process it belongs to. *}

type_synonym variable = "(name \<times> type \<times> expression)"

text {* sigprt denotes either a signal or a port. The VHDL RTL
often use "signal" for either of them. *}

datatype sigprt = sp_s signal |sp_p port

definition sigprt_type:: "sigprt \<Rightarrow> type" where
"sigprt_type sp \<equiv>
  case sp of 
   sp_s s \<Rightarrow> (fst (snd s))
  |sp_p p \<Rightarrow> (fst (snd p))"

text {* res_fn is the resolution function of the signal.
For a non-resolved signal, res_fn = None. 
In contrast to [1], we don't build res_fn into signals and ports. 
Instead, we define res_fn as a standalone function with sigport as a 
parameter. This way, we can avoid the wellsoortedness error in Isabelle
when we try to convert the code for execution. *}

type_synonym res_fn = "sigprt \<Rightarrow> ((val list) \<Rightarrow> val) option"

text {* We don't consider port-associations, since we assume an 
elaborated VHDL description. *}

type_synonym condition = expression

type_synonym sensitivity_list = "sigprt list"

text {* We don't consider pulse_rejection since the LEON3 design 
doesn't use it. *}

type_synonym choices = "expression list"

text {* The following defines the supported sequential statements. 
We do not consider assert statement and report statement. 

We only consider the funcitonal part of the VHDL lanuage, not the simulation
part. Thus we don't consider wait statement. *}

text {* We currently don't support other types of discrete_ranges. 
***** NOTE THAT *****
We restrict that expressions in discrete_range must be
of type natural. 
*}

datatype discrete_range = 
vhdl_dis_to expression expression (infixl "TO" 60)
|vhdl_dis_downto expression expression (infixl "DOWNTO" 60)

text {* More complex ways to assign signals/ports/variables.
***** NOTE THAT *****
We restrict that when using as_range expression range,
the range applied to the expression must match the length of the left hand side. 
***** NOTE THAT ******
We assume that a vector, when not initialised, is a list of val_null of the 
length that is equal to the declared length. 
That is, for a signal vector, its initial value is [val_null,...];
for a port vector, its initial expression is exp_con (type,[val_null,...]). 
**** NOTE ALSO THAT ***** 
Unlike expressions, the LHS of assignment (sp_lhs or v_lhs) do not have the form
s(n) where s is a signal/variable and n is a natural number indicating the 
index of the list. This form of assignment can be expressed as, e.g.,
lhs_sa (sp_s s) (n DOWNTO n) <= exp_sl e1 e2 e2.
THAT IS, We don't use exp_nth as the RHS in this form of assignment.
exp_nth is only used in the assignment of signals/variables of type equal to
the member of the list. e.g.,
lhs_s (sp_s s) <= exp_nth e1 e2.
*}

datatype sp_lhs =
lhs_s sigprt
|lhs_sa sigprt discrete_range

text {* Get the sigprt of sp_lhs. *}

definition exp_of_sp_lhs:: "sp_lhs \<Rightarrow> expression" where
"exp_of_sp_lhs lhs \<equiv> case lhs of 
  lhs_s (sp_s s) \<Rightarrow> exp_sig s 
  |lhs_sa (sp_s s) (e1 TO e2) \<Rightarrow> exp_sl (exp_sig s) e1 e2
  |lhs_sa (sp_s s) (e1 DOWNTO e2) \<Rightarrow> exp_sl (exp_sig s) e2 e1
  |lhs_s (sp_p p) \<Rightarrow> exp_prt p 
  |lhs_sa (sp_p p) (e1 TO e2) \<Rightarrow> exp_sl (exp_prt p) e1 e2
  |lhs_sa (sp_p p) (e1 DOWNTO e2) \<Rightarrow> exp_sl (exp_prt p) e2 e1"

datatype v_lhs =
lhs_v variable
|lhs_va variable discrete_range

datatype asmt_rhs = 
rhs_e expression  (* Just an expression. *)
|rhs_o expression ("(OTHERS => _)") (* (others => expression). *)
(*|rhs_er expression discrete_range ("_ \<langle>_\<rangle>")  expression(range). *)

text {* We currently treat a record in VHDL as a list of signals/ports/variables. 
We address the members of the record by matching the names of signals/ports/variables 
in the list. *}

text {* Convert a list of signals to a list of sigprts. *}

primrec sigprtl_of_sigl:: "signal list \<Rightarrow> sigprt list" where
"sigprtl_of_sigl [] = []"
|"sigprtl_of_sigl (s#sx) = (sp_s s)#(sigprtl_of_sigl sx)"

text {* Convert a list of signals to a list of ports. *}

primrec sigprtl_of_prtl:: "port list \<Rightarrow> sigprt list" where
"sigprtl_of_prtl [] = []"
|"sigprtl_of_prtl (p#px) = (sp_p p)#(sigprtl_of_prtl px)"

text {* We define the datatype sigprtl for record types of signals/ports. *}

datatype spl = 
spl_s signal
|spl_p port
|spnl "(name \<times> (spl list))"

definition list_of_spl:: "spl \<Rightarrow> spl list" where
"list_of_spl r \<equiv> case r of spnl (n,l) \<Rightarrow> l"

fun splist_of_spl:: "spl \<Rightarrow> sigprt list" where
"splist_of_spl (spl_s s) = [sp_s s]"
|"splist_of_spl (spl_p p) = [sp_p p]"
|"splist_of_spl (spnl (n,[])) = []"
|"splist_of_spl (spnl (n,(x#xs))) = (splist_of_spl x)@(splist_of_spl (spnl (n,xs)))"

text {* Search for a member in spl that has name n. Return spnl (n,[]) when fails. *}

fun spl_mem:: "spl \<Rightarrow> name \<Rightarrow> spl" (infixr "s." 65) where
"spl_mem (spl_s s) n = (
  if (fst s) = n then spl_s s
  else spnl (n,[])
)"
|"spl_mem (spl_p p) n = (
  if (fst p) = n then spl_p p
  else spnl (n,[])
)"
|"spl_mem (spnl nl1) n = (
  case nl1 of (n1,[]) \<Rightarrow> spnl (n,[])
  |(n1,(x#xs)) \<Rightarrow> (
    case spl_mem x n of spnl (_,[]) \<Rightarrow> spl_mem (spnl (n1,xs)) n
    |sp \<Rightarrow> sp
  )
)"

text {* Convert a spl to an expression. We only convert a spl 
if it's either a signal or a port. That is, we don't convert records. *}

definition exp_of_spl:: "spl \<Rightarrow> expression" where
"exp_of_spl l \<equiv> case l of 
  spl_s s \<Rightarrow> exp_sig s
  |spl_p p \<Rightarrow> exp_prt p"

definition sp_of_spl:: "spl \<Rightarrow> sigprt" where
"sp_of_spl l \<equiv> case l of
  spl_s s \<Rightarrow> sp_s s
  |spl_p p \<Rightarrow> sp_p p"

datatype vl =
vl_v variable
|vnl "(name \<times> (vl list))"

definition list_of_vl:: "vl \<Rightarrow> vl list" where
"list_of_vl r \<equiv> case r of vnl (n,l) \<Rightarrow> l"

fun vlist_of_vl:: "vl \<Rightarrow> variable list" where
"vlist_of_vl (vl_v v) = [v]"
|"vlist_of_vl (vnl (n,[])) = []"
|"vlist_of_vl (vnl (n,(x#xs))) = (vlist_of_vl x)@(vlist_of_vl (vnl (n,xs)))"

text {* Search for a member in spl that has name n. Return vnl (n,[]) when fails. *}

fun vl_mem:: "vl \<Rightarrow> name \<Rightarrow> vl" (infixr "v." 65) where
"vl_mem (vl_v v) n = (
  if (fst v) = n then vl_v v
  else vnl (n,[])
)"
|"vl_mem (vnl nl1) n = (
  case nl1 of (n1,[]) \<Rightarrow> vnl (n,[])
  |(n1,(x#xs)) \<Rightarrow> (
    case vl_mem x n of vnl (_,[]) \<Rightarrow> vl_mem (vnl (n1,xs)) n
    |v \<Rightarrow> v
  )
)"

text {* Convert a vl to an expression. We only convert a vl 
if it's a variable. That is, we don't convert records. *}

definition exp_of_vl:: "vl \<Rightarrow> expression" where
"exp_of_vl l \<equiv> case l of vl_v v \<Rightarrow> exp_var v"

definition var_of_vl:: "vl \<Rightarrow> variable" where
"var_of_vl l \<equiv> case l of vl_v v \<Rightarrow> v"

definition list_of_rhsl:: "rhsl \<Rightarrow> rhsl list" where
"list_of_rhsl r \<equiv> case r of rnl l \<Rightarrow> l"

text {* Convert a spl to a rhsl. *}

fun rhsl_of_spl:: "spl \<Rightarrow> rhsl" where
"rhsl_of_spl (spl_s s) = rl_s s"
|"rhsl_of_spl (spl_p p) = rl_p p"
|"rhsl_of_spl (spnl (n,[])) = rnl []"
|"rhsl_of_spl (spnl (n,(x#xs))) = 
  rnl ((rhsl_of_spl x)#(list_of_rhsl (rhsl_of_spl (spnl (n,xs)))))"

text {* Convert a vl to a rhsl. *}

fun rhsl_of_vl:: "vl \<Rightarrow> rhsl" where
"rhsl_of_vl (vl_v v) = rl_v v"
|"rhsl_of_vl (vnl (n,[])) = rnl []"
|"rhsl_of_vl (vnl (n,(x#xs))) = 
  rnl ((rhsl_of_vl x)#(list_of_rhsl (rhsl_of_vl (vnl (n,xs)))))"

datatype sp_clhs =
clhs_sp sp_lhs
|clhs_spr spl

datatype v_clhs =
clhs_v v_lhs
|clhs_vr vl

text {* A conversion from v_clhs to asmt_rhs. *}

definition asmt_rhs_of_v_clhs:: "v_clhs \<Rightarrow> asmt_rhs" where
"asmt_rhs_of_v_clhs lhs \<equiv> case lhs of 
  clhs_v (lhs_v v) \<Rightarrow> rhs_e (exp_var v)
  |clhs_v (lhs_va v (vhdl_dis_to e1 e2)) \<Rightarrow> rhs_e (exp_sl (exp_var v) e1 e2)
  |clhs_v (lhs_va v (vhdl_dis_downto e1 e2)) \<Rightarrow> rhs_e (exp_sl (exp_var v) e1 e2)
  |clhs_vr vl \<Rightarrow> rhs_e (exp_r (rhsl_of_vl vl))"

type_synonym subprogcall = "(name \<times> (v_clhs list) \<times> type)"

text {* Note that in the core model, we only permit function calls as statements of the form
v := functional call.
We DON'T allow function calls as expressions in the traditional form. 
In the complex model, we will translate function calls in expressions into the form we support. 
Furthermore, we restrict that the arguments in subprogram calls can only
be variables. Expressions in subprogram calls can be supported in the complex model.  *}

datatype seq_stmt = 
sst_sa name sp_clhs asmt_rhs (* Signal assignment. *)
|sst_va name v_clhs asmt_rhs (* Variable assignment. *)
|sst_if name condition "seq_stmt list" "seq_stmt list" (* If statement. *)
|sst_l name condition "seq_stmt list" (* While loop statement. *)
|sst_fn name v_clhs subprogcall
|sst_rt name asmt_rhs
|sst_pc name subprogcall
|sst_n name name condition (* Next statement. *)
|sst_e name name condition (* Exit statement. *)
|sst_nl (* Null statement. *)

text {* Since the keyword postponed doesn't occur in the LEON3 design, we assume
not_postponed for all postponement. *}

text {* We don't consider concurrent guarded signal assignments and
concurrent selected signal assignments, as the LEON3 design
don't use them. *}

text {* process-stmt = (name, sensitivity-list,
ordered-statements, set-of-drivers ). *}

text {* The following defines the supported concurrent statements.
We don't consider concurrent assert statement. 
We don't consider guarded block statement. Thus block statements 
can just be removed by unfolding them. *}

(* Concurrent process statement. *)
datatype conc_stmt = cst_ps name sensitivity_list "seq_stmt list" 

datatype statement = sst seq_stmt | cst conc_stmt

record environment = 
env_sp:: "sigprt list"
env_v:: "variable list"
env_t:: "type list"

type_synonym conc_stmt_list = "conc_stmt list"

datatype designator = dn_function | dn_procedure

datatype direction = dir_in | dir_out | dir_inout

type_synonym parameter = "(v_clhs \<times> direction \<times> type)"

type_synonym parameter_list = "parameter list"

type_synonym local_var_list = "v_clhs list"

text {* A subprogram contains its name, function/procedure, a list of parameters,
a list of sequential statements, and a return type (only for functions, 
we will use emptype for procedures). *}

type_synonym subprogram = "(name \<times> designator \<times> parameter_list \<times> (seq_stmt list) \<times> type \<times> local_var_list)"

text {* The definition of a VHDL description. *}

type_synonym vhdl_desc = "(environment \<times> res_fn \<times> conc_stmt_list \<times> subprogram list)"

text {* The vhdl_state is a snapshot of the values of signals, ports, and 
variables at a particular time (simulation cycle). Since we consider signals
with multiple drivers, we have to model effective values and driving values
of signals, which are not present in the ACL2 model. *}

record vhdl_state =
state_sp:: "sigprt \<Rightarrow> val option" (* Current value for signals/ports. *)
state_var:: "variable \<Rightarrow> val option" (* Current value for the variable. *)
state_eff_val:: "sigprt \<Rightarrow> val option" (* The effective value (i.e., next value)
for signals/ports. *)
state_dr_val:: "sigprt \<Rightarrow> conc_stmt \<Rightarrow> val option" 
(* Each signal/port has a driving value per process. The value is None if
the process doesn't drive it. *)
next_flag:: "(string \<times> bool)" (* The flag for the nearest next statement in effect. *)
exit_flag:: "(string \<times> bool)" (* The flag for the nearest exit statement in effect. *)

end