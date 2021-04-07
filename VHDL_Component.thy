(*
 * Copyright 2016, NTU
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * Author: Zhe Hou.
 *)

theory VHDL_Component
imports Main VHDL_Semantics
begin

text {* This file defines components in the VHDL model. 
The definition of a VHDL description for an architecture 
with components consists of a vhdl_desc and a name to identify this 
architecture. *}

type_synonym vhdl_arch_desc = "name \<times> vhdl_desc"

text {* vhdl_arch_desc_all contains all the architectures that this 
vhdl design involves. *}

type_synonym vhdl_arch_desc_all = "vhdl_arch_desc list"

text {* comp_port_map defines how the ports of a component is 
connected with the signals/ports of outer architecture. 
The first sigprt is a port of the component, 
the second sigprt is a signal/port of the outer architecture. *}

type_synonym comp_port_map = "sigprt \<Rightarrow> sigprt"

text {* Empty component port mapping. *}

definition emp_comp_port_map:: "comp_port_map" where "emp_comp_port_map \<equiv> \<lambda>x.(x)"

text {* Add a list of component port mappings to the current mapping. *}

primrec add_comp_port_map:: "(sigprt \<times> sigprt) list \<Rightarrow> comp_port_map \<Rightarrow>
  comp_port_map" where
"add_comp_port_map [] f = f"
|"add_comp_port_map (x#xs) f = add_comp_port_map xs (f((fst x) := (snd x)))"

text {* The state of an architecture with components consists of 
the name of the architecture, the elements of the state,
and a list of sub-states for component instances. *}

datatype vhdl_arch_state =
arch_state "(name \<times> vhdl_state \<times> (comp_port_map \<times> vhdl_arch_state) list)" 

definition state_of_arch:: "vhdl_arch_state \<Rightarrow> vhdl_state" where
"state_of_arch state \<equiv> case state of arch_state (n,s,cl) \<Rightarrow> s"

definition comps_of_arch:: "vhdl_arch_state \<Rightarrow> (comp_port_map \<times> vhdl_arch_state) list"
where "comps_of_arch state \<equiv> case state of arch_state (n,s,cl) \<Rightarrow> cl"

text {* Obtain the description of an architecture by matching its name. *}

primrec get_desc:: "vhdl_arch_desc_all \<Rightarrow> vhdl_arch_state \<Rightarrow> vhdl_desc option" where
"get_desc [] state = None"
|"get_desc (x#xs) state = (
  case state of arch_state s \<Rightarrow>
    if (fst x) = (fst s) then Some (snd x)
    else get_desc xs state
)"

text {* Obtain the list of input ports from a list of sigprt. *}

primrec get_inport:: "sigprt list \<Rightarrow> sigprt list" where
"get_inport [] = []"
|"get_inport (x#xs) = (
  case x of sp_s s \<Rightarrow> get_inport xs
  |sp_p p \<Rightarrow> (
    if (fst (snd (snd p))) = mode_in then 
      x#(get_inport xs) 
    else get_inport xs
))"

text {* Obtain the list of output ports from a list of sigprt. *}

primrec get_outport:: "sigprt list \<Rightarrow> sigprt list" where
"get_outport [] = []"
|"get_outport (x#xs) = (
  case x of sp_s s \<Rightarrow> get_outport xs
  |sp_p p \<Rightarrow> (
    if (fst (snd (snd p))) = mode_out then 
      x#(get_outport xs) 
    else get_outport xs
))"

text {* Pass an actual port value from the outer architecture to a component. *}

primrec pass_input:: "vhdl_state \<Rightarrow> sigprt list \<Rightarrow> comp_port_map \<Rightarrow>
  vhdl_state \<Rightarrow> vhdl_state" where
"pass_input s1 [] m s2 = s2"
|"pass_input s1 (x#xs) m s2 = 
  pass_input s1 xs m (s2\<lparr>state_sp := (state_sp s2)(x := ((state_sp s1) (m x)))\<rparr>)
"

text {* Pass actual port values from the outer architecture to a component. 
Return the state of the component. *}

definition pass_input_all:: "vhdl_arch_desc_all \<Rightarrow> vhdl_arch_state \<Rightarrow> 
  (comp_port_map \<times> vhdl_arch_state) \<Rightarrow> vhdl_arch_state" where
"pass_input_all descs state cpo \<equiv> 
  let this_desc = get_desc descs state;
      cpo_desc = get_desc descs (snd cpo) in
  case (this_desc,cpo_desc) of (Some this_d, Some cpo_d) \<Rightarrow> (
    case (state,(snd cpo)) of ((arch_state (n1,s1,l1)),(arch_state (n2,s2,l2))) \<Rightarrow>
    arch_state (n2,(pass_input s1 (get_inport (env_sp (fst cpo_d))) (fst cpo) s2),l2)
  )
  | _ \<Rightarrow> (snd cpo)
"

text {* Pass all input values to all the components. 
Return the list of components. *}

primrec pass_input_all_comps:: "vhdl_arch_desc_all \<Rightarrow> vhdl_arch_state \<Rightarrow>
  (comp_port_map \<times> vhdl_arch_state) list \<Rightarrow> (comp_port_map \<times> vhdl_arch_state) list" where
"pass_input_all_comps descs state [] = []"
|"pass_input_all_comps descs state (x#xs) =
  ((fst x),(pass_input_all descs state x))#(pass_input_all_comps descs state xs)
"

text {* Get the values of a list of signal/ports from a state. 
Return a list of (sigprt,val option) pairs. *}

primrec get_sigprt_val:: "vhdl_state \<Rightarrow> sigprt list \<Rightarrow> (sigprt \<times> (val option)) list" where
"get_sigprt_val state [] = []"
|"get_sigprt_val state (x#xs) = (x,((state_sp state) x))#(get_sigprt_val state xs)"

text {* Get output port values from a state. Return a list of (sigprt,val option) pairs
where sigprt is an output port of the state. *}

definition get_output_val:: "vhdl_desc \<Rightarrow> vhdl_state \<Rightarrow> (sigprt \<times> (val option)) list" where
"get_output_val desc state \<equiv>
  let outports = get_outport (env_sp (fst desc)) in
  get_sigprt_val state outports"

text {* Map the output ports of a component to the 
connected ports of the outer architecture. *}

primrec map_output_vals:: "comp_port_map \<Rightarrow> (sigprt \<times> (val option)) list \<Rightarrow>
  (sigprt \<times> (val option)) list" where
"map_output_vals m [] = []"
|"map_output_vals m (x#xs) = ((m (fst x)),(snd x))#(map_output_vals m xs)"

text {* Get the result of a component after its executed for 1 cycle. 
The sigprt is *NOT* the output port of the component, but
the connected port in the outer architectre. *}

definition get_comp_result:: "vhdl_arch_desc_all \<Rightarrow> (comp_port_map \<times> vhdl_arch_state) \<Rightarrow> 
  (sigprt \<times> (val option)) list" where
"get_comp_result descs cpo \<equiv> 
  let this_desc = get_desc descs (snd cpo) in
  case this_desc of Some d \<Rightarrow> (
    let output_vals = get_output_val d (state_of_arch (snd cpo)) in
    map_output_vals (fst cpo) output_vals)
  |None \<Rightarrow> []
"

text {* get the output results from a list of components. 
The sigprt is *NOT* the output port of the component, but
the connected port in the outer architectre.*}

primrec get_comp_result_all:: "vhdl_arch_desc_all \<Rightarrow> (comp_port_map \<times> vhdl_arch_state) list \<Rightarrow> 
  (sigprt \<times> (val option)) list" where 
"get_comp_result_all descs [] = []"
|"get_comp_result_all descs (x#xs) = (get_comp_result descs x)@(get_comp_result_all descs xs)"

text {* Given a list of (sigprt,val option) pairs, where sigprt is the 
connected port of the outer architecture, return a list of (sigprt, val list) pairs
where each sigprt only occurs once. *}

primrec insert_comp_result:: "(sigprt \<times> (val option)) \<Rightarrow> (sigprt \<times> (val list)) list \<Rightarrow>
 (sigprt \<times> (val list)) list" where
"insert_comp_result sv [] = (
  case snd sv of Some v \<Rightarrow> [((fst sv),[v])]
  |None \<Rightarrow> [((fst sv),[])])"
|"insert_comp_result sv (x#xs) = (
  if fst sv = fst x then 
    case snd sv of Some v \<Rightarrow> ((fst x),(v#(snd x)))#xs
    |None \<Rightarrow> x#xs
  else x#(insert_comp_result sv xs)
)"

primrec collect_comp_result_all:: "(sigprt \<times> (val option)) list \<Rightarrow> (sigprt \<times> (val list)) list \<Rightarrow>
  (sigprt \<times> (val list)) list" where
"collect_comp_result_all [] rl = rl"
|"collect_comp_result_all (x#xs) rl = 
  collect_comp_result_all xs (insert_comp_result x rl)"

text {* Use the resolution function from the outer architecture
to resolve the signals passed from the components. *}

primrec resolve_comp_result_all:: "res_fn \<Rightarrow> (sigprt \<times> (val list)) list \<Rightarrow>
  (sigprt \<times> (val option)) list" where
"resolve_comp_result_all rf [] = []"
|"resolve_comp_result_all rf (x#xs) = (
  if length (snd x) = 1 then ((fst x),Some (hd (snd x)))#(resolve_comp_result_all rf xs)
  else if length (snd x) = 0 then ((fst x),None)#(resolve_comp_result_all rf xs)
  else (* This port of the outer architecture is connected to more than one components. *)
    case rf (fst x) of Some f \<Rightarrow> ((fst x),Some (f (snd x)))#(resolve_comp_result_all rf xs)
    |None \<Rightarrow> ((fst x),None)#(resolve_comp_result_all rf xs))"

text {* Pass the component results to the outer architecture. *}

primrec pass_output_all:: "vhdl_state \<Rightarrow> (sigprt \<times> (val option)) list \<Rightarrow> vhdl_state" where
"pass_output_all state [] = state"
|"pass_output_all state (x#xs) = (
  pass_output_all (state\<lparr>state_sp := (state_sp state)((fst x) := (snd x))\<rparr>) xs)
"

definition get_comp_result_state:: "vhdl_arch_desc_all \<Rightarrow> vhdl_arch_state \<Rightarrow> vhdl_arch_state"
where "get_comp_result_state descs state \<equiv>
  case get_desc descs state of Some d \<Rightarrow> (
    case state of arch_state (n,s,cl) \<Rightarrow>
      let comp_results = get_comp_result_all descs cl;
          collected_values = collect_comp_result_all comp_results [];
          resolved_values = resolve_comp_result_all (fst (snd d)) collected_values;
          ns = pass_output_all s resolved_values 
      in
      arch_state (n,ns,cl))
  |None \<Rightarrow> state (* This architecture doesn't have a description. Wrong definition. *)
"

function (sequential) sim_arch:: "nat \<Rightarrow> vhdl_arch_desc_all \<Rightarrow> vhdl_arch_state \<Rightarrow> vhdl_arch_state" 
and sim_comps:: "vhdl_arch_desc_all \<Rightarrow> (comp_port_map \<times> vhdl_arch_state) list \<Rightarrow> 
  (comp_port_map \<times> vhdl_arch_state) list" where
"sim_arch 0 descs state = state"
|"sim_arch n descs state = (
  let this_desc = get_desc descs state in
  case this_desc of Some d \<Rightarrow> (
    case state of arch_state s \<Rightarrow>
      if (snd (snd s)) = [] then 
        (* If this architecture doesn't have component instances, 
        then simulate it for 1 cycle as before. *)
        let ns = arch_state ((fst s),(simulation 1 d (fst (snd s))),[]) in
        sim_arch (n-1) descs ns
      else 
        (* This architecture has component instances. *)        
        (* Pass the input from the outer architecture to each component. *)
        let new_cl = pass_input_all_comps descs state (snd (snd s));
        (* Simulate each component. *)
            sim_cl = sim_comps descs new_cl;
        (* Pass the output of each component to the outer architecture. *)
            output_s = get_comp_result_state descs (arch_state ((fst s),(fst (snd s)),sim_cl));
        (* Simulate the outer architecture for 1 cycle. *)
            ns = arch_state ((fst s),(simulation 1 d (state_of_arch output_s)),(comps_of_arch output_s))
        in
        sim_arch (n-1) descs ns          
    )
  |None \<Rightarrow> state
  )"
|"sim_comps descs [] = []"
|"sim_comps descs (x#xs) = ((fst x),(sim_arch 1 descs (snd x)))#(sim_comps descs xs)"
by pat_completeness auto 
termination sorry

end