(*
 * Copyright 2016, NTU
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * Author: Zhe Hou.
 *)

theory VHDL_Div32
imports Main VHDL_Component VHDL_Syntax_Complex
begin

text {* This file is a manually translated vhdl code from div32.vhd in Gaisler's lib. *}

definition scantest:: "variable" where
"scantest \<equiv> (''scantest'', vhdl_integer, (exp_con (vhdl_integer, (val_i 0))))"

definition rst:: "port" where
"rst \<equiv> (''rst'', vhdl_std_ulogic, mode_in, connected, 
  (exp_con (vhdl_std_ulogic, (val_c (CHR ''1'')))))"

definition holdn:: "port" where
"holdn \<equiv> (''holdn'', vhdl_std_ulogic, mode_in, connected, 
  (exp_con (vhdl_std_ulogic, (val_c (CHR ''1'')))))"

definition divi:: "spl" where
"divi \<equiv> spnl ('''',[
  spl_p (''divi_y'', vhdl_std_logic_vector, mode_in, connected, 
    (exp_con (vhdl_std_logic_vector, (val_rlist (std_logic_vec_gen 33 (val_c (CHR ''0''))))))),
  spl_p (''divi_op1'', vhdl_std_logic_vector, mode_in, connected, 
    (exp_con (vhdl_std_logic_vector, (val_rlist (* Binary of 18. *)
      ((std_logic_vec_gen 28 (val_c (CHR ''0'')))
      @[(val_c (CHR ''1'')),(val_c (CHR ''0'')),(val_c (CHR ''0'')),(val_c (CHR ''1'')),(val_c (CHR ''0''))]))))),
  spl_p (''divi_op2'', vhdl_std_logic_vector, mode_in, connected, 
    (exp_con (vhdl_std_logic_vector, (val_rlist (* Binary of 2. *)
      ((std_logic_vec_gen 31 (val_c (CHR ''0'')))
      @[(val_c (CHR ''1'')),(val_c (CHR ''0''))]))))),
  spl_p (''divi_flush'', vhdl_std_logic, mode_in, connected, 
    (exp_con (vhdl_std_logic, (val_c (CHR ''0''))))),
  spl_p (''divi_signed'', vhdl_std_logic, mode_in, connected, 
    (exp_con (vhdl_std_logic, (val_c (CHR ''0''))))),
  spl_p (''divi_start'', vhdl_std_logic, mode_in, connected, 
    (exp_con (vhdl_std_logic, (val_c (CHR ''1'')))))
])"

definition divo:: "spl" where
"divo \<equiv> spnl ('''',[
  spl_p (''divo_ready'', vhdl_std_logic, mode_out, connected, 
    (exp_con (vhdl_std_logic, (val_c (CHR ''0''))))),
  spl_p (''divo_nready'', vhdl_std_logic, mode_out, connected, 
    (exp_con (vhdl_std_logic, (val_c (CHR ''0''))))),
  spl_p (''divo_icc'', vhdl_std_logic_vector, mode_out, connected, 
    (exp_con (vhdl_std_logic_vector, (val_rlist (std_logic_vec_gen 4 (val_c (CHR ''0''))))))),
  spl_p (''divo_result'', vhdl_std_logic_vector, mode_out, connected, 
    (exp_con (vhdl_std_logic_vector, (val_rlist (std_logic_vec_gen 32 (val_c (CHR ''0'')))))))
])"

definition testen:: "port" where
"testen \<equiv> (''testen'', vhdl_std_ulogic, mode_in, connected, 
  (exp_con (vhdl_std_ulogic, (val_c (CHR ''0'')))))"

definition testrst:: "port" where
"testrst \<equiv> (''testrst'', vhdl_std_ulogic, mode_in, connected, 
  (exp_con (vhdl_std_ulogic, (val_c (CHR ''1'')))))"

definition reset_all:: "variable" where
"reset_all \<equiv> (''RESET_ALL'', vhdl_boolean, (exp_con (vhdl_boolean, (val_b True))))"

definition async_reset:: "variable" where
"async_reset \<equiv> (''ASYNC_RESET'', vhdl_boolean, (exp_con (vhdl_boolean, (val_b True))))"

definition rres:: "vl" where
"rres \<equiv> vnl ('''',[
  vl_v (''rres_x'', vhdl_std_logic_vector, (exp_con (vhdl_std_logic_vector, (val_rlist (std_logic_vec_gen 65 (val_c (CHR ''0''))))))),
  vl_v (''rres_state'', vhdl_std_logic_vector, (exp_con (vhdl_std_logic_vector, (val_rlist (std_logic_vec_gen 3 (val_c (CHR ''0''))))))),
  vl_v (''rres_zero'', vhdl_std_logic, (exp_con (vhdl_std_logic, (val_c (CHR ''0''))))),
  vl_v (''rres_zero2'', vhdl_std_logic, (exp_con (vhdl_std_logic, (val_c (CHR ''0''))))),
  vl_v (''rres_qcorr'', vhdl_std_logic, (exp_con (vhdl_std_logic, (val_c (CHR ''0''))))),
  vl_v (''rres_zcorr'', vhdl_std_logic, (exp_con (vhdl_std_logic, (val_c (CHR ''0''))))),
  vl_v (''rres_qzero'', vhdl_std_logic, (exp_con (vhdl_std_logic, (val_c (CHR ''0''))))),
  vl_v (''rres_qmsb'', vhdl_std_logic, (exp_con (vhdl_std_logic, (val_c (CHR ''0''))))),
  vl_v (''rres_ovf'', vhdl_std_logic, (exp_con (vhdl_std_logic, (val_c (CHR ''0''))))),
  vl_v (''rres_neg'', vhdl_std_logic, (exp_con (vhdl_std_logic, (val_c (CHR ''0''))))),
  vl_v (''rres_cnt'', vhdl_std_logic_vector, (exp_con (vhdl_std_logic_vector, (val_rlist (std_logic_vec_gen 5 (val_c (CHR ''0'')))))))
])"

definition arst:: "signal" where
"arst \<equiv> (''arst'', vhdl_std_ulogic, register, (exp_con (vhdl_std_ulogic, (val_c (CHR ''1'')))))"

definition r:: "spl" where
"r \<equiv> spnl ('''',[
  spl_s (''r_x'', vhdl_std_logic_vector, register, (exp_con (vhdl_std_logic_vector, (val_rlist (std_logic_vec_gen 65 (val_c (CHR ''0''))))))),
  spl_s (''r_state'', vhdl_std_logic_vector, register, (exp_con (vhdl_std_logic_vector, (val_rlist (std_logic_vec_gen 3 (val_c (CHR ''0''))))))),
  spl_s (''r_zero'', vhdl_std_logic, register, (exp_con (vhdl_std_logic, (val_c (CHR ''0''))))),
  spl_s (''r_zero2'', vhdl_std_logic, register, (exp_con (vhdl_std_logic, (val_c (CHR ''0''))))),
  spl_s (''r_qcorr'', vhdl_std_logic, register, (exp_con (vhdl_std_logic, (val_c (CHR ''0''))))),
  spl_s (''r_zcorr'', vhdl_std_logic, register, (exp_con (vhdl_std_logic, (val_c (CHR ''0''))))),
  spl_s (''r_qzero'', vhdl_std_logic, register, (exp_con (vhdl_std_logic, (val_c (CHR ''0''))))),
  spl_s (''r_qmsb'', vhdl_std_logic, register, (exp_con (vhdl_std_logic, (val_c (CHR ''0''))))),
  spl_s (''r_ovf'', vhdl_std_logic, register, (exp_con (vhdl_std_logic, (val_c (CHR ''0''))))),
  spl_s (''r_neg'', vhdl_std_logic, register, (exp_con (vhdl_std_logic, (val_c (CHR ''0''))))),
  spl_s (''r_cnt'', vhdl_std_logic_vector, register, (exp_con (vhdl_std_logic_vector, (val_rlist (std_logic_vec_gen 5 (val_c (CHR ''0'')))))))
])"

definition rin:: "spl" where 
"rin \<equiv> spnl ('''',[
  spl_s (''rin_x'', vhdl_std_logic_vector, register, (exp_con (vhdl_std_logic_vector, (val_rlist (std_logic_vec_gen 65 (val_c (CHR ''0''))))))),
  spl_s (''rin_state'', vhdl_std_logic_vector, register, (exp_con (vhdl_std_logic_vector, (val_rlist (std_logic_vec_gen 3 (val_c (CHR ''0''))))))),
  spl_s (''rin_zero'', vhdl_std_logic, register, (exp_con (vhdl_std_logic, (val_c (CHR ''0''))))),
  spl_s (''rin_zero2'', vhdl_std_logic, register, (exp_con (vhdl_std_logic, (val_c (CHR ''0''))))),
  spl_s (''rin_qcorr'', vhdl_std_logic, register, (exp_con (vhdl_std_logic, (val_c (CHR ''0''))))),
  spl_s (''rin_zcorr'', vhdl_std_logic, register, (exp_con (vhdl_std_logic, (val_c (CHR ''0''))))),
  spl_s (''rin_qzero'', vhdl_std_logic, register, (exp_con (vhdl_std_logic, (val_c (CHR ''0''))))),
  spl_s (''rin_qmsb'', vhdl_std_logic, register, (exp_con (vhdl_std_logic, (val_c (CHR ''0''))))),
  spl_s (''rin_ovf'', vhdl_std_logic, register, (exp_con (vhdl_std_logic, (val_c (CHR ''0''))))),
  spl_s (''rin_neg'', vhdl_std_logic, register, (exp_con (vhdl_std_logic, (val_c (CHR ''0''))))),
  spl_s (''rin_cnt'', vhdl_std_logic_vector, register, (exp_con (vhdl_std_logic_vector, (val_rlist (std_logic_vec_gen 5 (val_c (CHR ''0'')))))))
])"

definition addin1:: "signal" where
"addin1 \<equiv> (''addin1'', vhdl_std_logic_vector, register, 
  (exp_con (vhdl_std_logic_vector, (val_list (std_logic_vec_gen 33 (val_c (CHR ''0'')))))))"

definition addin2:: "signal" where
"addin2 \<equiv> (''addin2'', vhdl_std_logic_vector, register, 
  (exp_con (vhdl_std_logic_vector, (val_rlist (std_logic_vec_gen 33 (val_c (CHR ''0'')))))))"

definition addout:: "signal" where
"addout \<equiv> (''addout'', vhdl_std_logic_vector, register, 
  (exp_con (vhdl_std_logic_vector, (val_rlist (std_logic_vec_gen 33 (val_c (CHR ''0'')))))))"

definition c:: "variable" where
"c \<equiv> (''c'', vhdl_array,                    
  (exp_con (vhdl_array, (val_list (std_logic_vec_gen 4 (val_b True))))))"

definition addsub:: "signal" where
"addsub \<equiv> (''addsub'', vhdl_std_logic, register, (exp_con (vhdl_std_logic, (val_c (CHR ''0'')))))"

definition v:: "vl" where
"v \<equiv> vnl ('''',[
  vl_v (''v_x'', vhdl_std_logic_vector, (exp_con (vhdl_std_logic_vector, (val_rlist (std_logic_vec_gen 65 (val_c (CHR ''0''))))))),
  vl_v (''v_state'', vhdl_std_logic_vector, (exp_con (vhdl_std_logic_vector, (val_rlist (std_logic_vec_gen 3 (val_c (CHR ''0''))))))),
  vl_v (''v_zero'', vhdl_std_logic, (exp_con (vhdl_std_logic, (val_c (CHR ''0''))))),
  vl_v (''v_zero2'', vhdl_std_logic, (exp_con (vhdl_std_logic, (val_c (CHR ''0''))))),
  vl_v (''v_qcorr'', vhdl_std_logic, (exp_con (vhdl_std_logic, (val_c (CHR ''0''))))),
  vl_v (''v_zcorr'', vhdl_std_logic, (exp_con (vhdl_std_logic, (val_c (CHR ''0''))))),
  vl_v (''v_qzero'', vhdl_std_logic, (exp_con (vhdl_std_logic, (val_c (CHR ''0''))))),
  vl_v (''v_qmsb'', vhdl_std_logic, (exp_con (vhdl_std_logic, (val_c (CHR ''0''))))),
  vl_v (''v_ovf'', vhdl_std_logic, (exp_con (vhdl_std_logic, (val_c (CHR ''0''))))),
  vl_v (''v_neg'', vhdl_std_logic, (exp_con (vhdl_std_logic, (val_c (CHR ''0''))))),
  vl_v (''v_cnt'', vhdl_std_logic_vector, (exp_con (vhdl_std_logic_vector, (val_rlist (std_logic_vec_gen 5 (val_c (CHR ''0'')))))))
])"

definition vready:: "variable" where
"vready \<equiv> (''vready'', vhdl_std_logic, (exp_con (vhdl_std_logic, (val_c (CHR ''0'')))))"

definition vnready:: "variable" where
"vnready \<equiv> (''vnready'', vhdl_std_logic, (exp_con (vhdl_std_logic, (val_c (CHR ''0'')))))"

definition vaddin1:: "variable" where
"vaddin1 \<equiv> (''vaddin1'', vhdl_std_logic_vector, 
  (exp_con (vhdl_std_logic_vector, (val_rlist (std_logic_vec_gen 33 (val_c (CHR ''0'')))))))"

definition vaddin2:: "variable" where
"vaddin2 \<equiv> (''vaddin2'', vhdl_std_logic_vector, 
  (exp_con (vhdl_std_logic_vector, (val_rlist (std_logic_vec_gen 33 (val_c (CHR ''0'')))))))"

definition vaddsub:: "variable" where
"vaddsub \<equiv> (''vaddsub'', vhdl_std_logic, (exp_con (vhdl_std_logic, (val_c (CHR ''0'')))))"

definition ymsb:: "variable" where
"ymsb \<equiv> (''ymsb'', vhdl_std_logic, (exp_con (vhdl_std_logic, (val_c (CHR ''0'')))))"

definition zero33:: "variable" where
"zero33 \<equiv> (''zero33'', vhdl_std_logic_vector, 
  (exp_con (vhdl_std_logic_vector, (val_rlist (std_logic_vec_gen 33 (val_c (CHR ''0'')))))))"

definition b:: "variable" where
"b \<equiv> (''b'', vhdl_std_logic_vector, 
  (exp_con (vhdl_std_logic_vector, (val_rlist (std_logic_vec_gen 33 (val_c (CHR ''0'')))))))"

definition div32:: "vhdl_desc_complex" where
"div32 \<equiv>
  let env = \<lparr>env_sp = [sp_p rst, sp_p p_clk, sp_p holdn]@(splist_of_spl divi)
                      @(splist_of_spl divo)@[sp_p testen, sp_p testrst,
                      sp_s arst]@(splist_of_spl r)@(splist_of_spl rin)
                      @[sp_s addin1, sp_s addin2, sp_s addout, sp_s addsub],
             env_v = [scantest, reset_all, async_reset]@(vlist_of_vl rres)
                      @(vlist_of_vl v)@[vready, vnready, 
                      vaddin1, vaddin2, vaddsub, ymsb, zero33, b],
             env_t = []\<rparr>;
      resfn = \<lambda>x.(None); (* May need to use the resolution function for std_ulogic. *)
      cst_list = [
        ('''': (clhs_sp (lhs_s (sp_s arst))) <= <[((rhs_e (exp_prt testrst)) WHEN 
                                 (bexpl (exp_var async_reset) [and] (bexpl 
                                  (bexpr (exp_var scantest) [/=] (exp_con (vhdl_integer, (val_i 0)))) [and] 
                                  (bexpr (exp_prt testen) [/=] (eul (CHR ''0''))))) ELSE),
                               ((rhs_e (exp_prt rst)) WHEN (exp_var async_reset) ELSE)]> 
                              (rhs_e (eul (CHR ''1'')))),
        (''divcomb'': PROCESS ((splist_of_spl r)@[sp_p rst]@(splist_of_spl divi)@[sp_s addout])
         BEGIN [
          ('''': (clhs_v (lhs_v vready)) := (rhs_e (el (CHR ''0'')))),
          ('''': (clhs_v (lhs_v vnready)) := (rhs_e (el (CHR ''0'')))),
          ('''': (clhs_vr v) := (rhs_e (exp_r (rhsl_of_spl r)))),
          ('''': IF (bexpr (exp_sig addout) [=] (exp_var zero33)) 
                 THEN [('''': (clhs_v (lhs_v (var_of_vl (v v.''v_zero'')))) := (rhs_e (el (CHR ''1''))))] 
                 [] ELSE [('''': (clhs_v (lhs_v (var_of_vl (v v.''v_zero'')))) := (rhs_e (el (CHR ''0''))))] 
                 END IF),
          ('''': (clhs_v(lhs_v vaddin1)) := (rhs_e (exp_sl (exp_of_spl (r s.''r_x'')) (en 31) 
            (en 63)))),
          ('''': (clhs_v (lhs_v vaddin2)) := (rhs_e (exp_of_spl (divi s.''divi_op2'')))),
          ('''': (clhs_v (lhs_v vaddsub)) := (rhs_e (uexp [not] (bexpl (exp_nth (exp_of_spl (divi s.''divi_op2'')) 
            (en 32)) [xor] 
            (exp_nth (exp_of_spl (r s.''r_x'')) (en 64)))))),
          ('''': (clhs_v (lhs_v (var_of_vl (v v.''v_zero2'')))) := (rhs_e (exp_of_spl (r s.''r_zero'')))),
          ('''': CASE (exp_of_spl (r s.''r_state'')) IS [
            (WHEN [elrl [(val_c (CHR ''0'')),(val_c (CHR ''0'')),(val_c (CHR ''0''))]] => [
              ('''': (clhs_v (lhs_v (var_of_vl (v v.''v_cnt'')))) := (rhs_e (elrl [(val_c (CHR ''0'')),(val_c (CHR ''0'')),
                (val_c (CHR ''0'')),(val_c (CHR ''0'')),(val_c (CHR ''0''))]))),
              ('''': IF (bexpr (exp_of_spl (divi s.''divi_start'')) [=] (el (CHR ''1''))) 
                THEN [
                  ('''': (clhs_v (lhs_va (var_of_vl (v v.''v_x'')) ((en 64) DOWNTO (en 64)))) :=
                   (rhs_e (exp_sl (exp_of_spl (divi s.''divi_y'')) (en 32) (en 32)))),
                  ('''': (clhs_v (lhs_v (var_of_vl (v v.''v_state'')))) := (rhs_e (elrl [(val_c (CHR ''0'')),
                    (val_c (CHR ''0'')),(val_c (CHR ''1''))])))
                ] [] ELSE [] END IF)
              ]),
            (WHEN [elrl [(val_c (CHR ''0'')),(val_c (CHR ''0'')),(val_c (CHR ''1''))]] => [
              ('''': (clhs_v (lhs_v (var_of_vl (v v.''v_x'')))) := (rhs_e (bexpa (exp_of_spl (divi s.''divi_y'')) [&] 
                (exp_sl (exp_of_spl (divi s.''divi_op1'')) (en 0) (en 31))))),
              ('''': (clhs_v (lhs_v (var_of_vl (v v.''v_neg'')))) := (rhs_e (bexpl (exp_nth (exp_of_spl (divi s.''divi_op2'')) 
                (en 32)) [xor] (exp_nth (exp_of_spl (divi s.''divi_y'')) (en 32))))),
              ('''': IF (bexpr (exp_of_spl (divi s.''divi_signed'')) [=] 
                (el (CHR ''1''))) THEN [
                  ('''': (clhs_v (lhs_v vaddin1)) := (rhs_e (bexpa (exp_sl (exp_of_spl (divi s.''divi_y'')) 
                    (en 0) (en 31)) [&] (exp_sl (exp_of_spl (divi s.''divi_op1'')) (en 31) (en 31))))),
                  ('''': (clhs_v (lhs_v (var_of_vl (v v.''v_ovf'')))) := (rhs_e (uexp [not] 
                    (bexpl (exp_nth (exp_sig addout) (en 32)) [xor] 
                    (exp_nth (exp_of_spl (divi s.''divi_y'')) (en 32))))))
                ] [] ELSE [
                  ('''': (clhs_v (lhs_v vaddin1)) := (rhs_e (exp_of_spl (divi s.''divi_y'')))),
                  ('''': (clhs_v (lhs_v vaddsub)) := (rhs_e (el (CHR ''1'')))),
                  ('''': (clhs_v (lhs_v (var_of_vl (v v.''v_ovf'')))) := (rhs_e 
                    (uexp [not] (exp_nth (exp_sig addout) (en 32)))))
                ] END IF),
              ('''': (clhs_v (lhs_v (var_of_vl (v v.''v_state'')))) := (rhs_e (elrl [(val_c (CHR ''0'')),(val_c (CHR ''1'')),
                (val_c (CHR ''0''))])))
              ]),
            (WHEN [elrl [(val_c (CHR ''0'')),(val_c (CHR ''1'')),(val_c (CHR ''0''))]] => [
              ('''': IF (bexpl (bexpr (bexpl (exp_of_spl (divi s.''divi_signed'')) [and] 
                (bexpl (exp_of_spl (r s.''r_neg'')) [and] 
                (exp_of_spl (r s.''r_zero'')))) [=] (el (CHR ''1''))) [and] 
                (bexpr (exp_of_spl (divi s.''divi_op1'')) [=] (exp_var zero33))) THEN [
                ('''': (clhs_v (lhs_v (var_of_vl (v v.''v_ovf'')))) := (rhs_e (el (CHR ''0''))))
                ] [] ELSE [] END IF),
              ('''': (clhs_v (lhs_v (var_of_vl (v v.''v_qmsb'')))) := (rhs_e (exp_var vaddsub))),
              ('''': (clhs_v (lhs_v (var_of_vl (v v.''v_qzero'')))) := (rhs_e (el (CHR ''1'')))),
              ('''': (clhs_v (lhs_va (var_of_vl (v v.''v_x'')) ((en 64) DOWNTO (en 32)))) := (rhs_e (exp_sig addout))),
              ('''': (clhs_v (lhs_va (var_of_vl (v v.''v_x'')) ((en 31) DOWNTO (en 0)))) := 
                (rhs_e (bexpa (exp_sl (exp_of_spl (r s.''r_x'')) (en 0) (en 30)) [&] 
                (exp_trl (exp_var vaddsub))))), 
              ('''': (clhs_v (lhs_v (var_of_vl (v v.''v_state'')))) := (rhs_e (elrl [(val_c (CHR ''0'')),
                (val_c (CHR ''1'')),(val_c (CHR ''1''))]))),
              ('''': (clhs_v (lhs_v (var_of_vl (v v.''v_zcorr'')))) := (rhs_e (exp_of_vl (v v.''v_zero'')))),
              ('''': (clhs_v (lhs_v (var_of_vl (v v.''v_cnt'')))) := (rhs_e (bexpa (exp_of_spl (r s. ''r_cnt'')) [+] 
                (elrl [val_c (CHR ''1'')]))))
              ]),
            (WHEN [elrl [(val_c (CHR ''0'')),(val_c (CHR ''1'')),(val_c (CHR ''1''))]] => [
              ('''': (clhs_v (lhs_v (var_of_vl (v v.''v_qzero'')))) := (rhs_e (bexpl (exp_of_spl (r s.''r_qzero'')) [and] 
                (bexpl (exp_var vaddsub) [xor] (exp_of_spl (r s.''r_qmsb'')))))),
              ('''': (clhs_v (lhs_v (var_of_vl (v v.''v_zcorr'')))) := (rhs_e (bexpl (exp_of_spl (r s.''r_zcorr'')) [or] 
                (exp_of_vl (v v.''v_zero''))))),
              ('''': (clhs_v (lhs_va (var_of_vl (v v.''v_x'')) ((en 64) DOWNTO (en 32)))) := (rhs_e (exp_sig addout))),
              ('''': (clhs_v (lhs_va (var_of_vl (v v.''v_x'')) ((en 31) DOWNTO (en 0)))) := 
                (rhs_e (bexpa (exp_sl (exp_of_spl (r s.''r_x'')) (en 0) (en 30)) [&] 
                (exp_trl (exp_var vaddsub))))), 
              ('''': IF (bexpr (exp_of_spl (r s.''r_cnt'')) [=] 
                (elrl [(val_c (CHR ''1'')),(val_c (CHR ''1'')),(val_c (CHR ''1'')),(val_c (CHR ''1'')),
                (val_c (CHR ''1''))])) THEN [
                  ('''': (clhs_v (lhs_v (var_of_vl (v v.''v_state'')))) := (rhs_e (elrl [(val_c (CHR ''1'')),
                    (val_c (CHR ''0'')),(val_c (CHR ''0''))]))),
                  ('''': (clhs_v (lhs_v vnready)) := (rhs_e (el (CHR ''1''))))
                ] [] ELSE [
                  ('''': (clhs_v (lhs_v (var_of_vl (v v.''v_cnt'')))) := (rhs_e (bexpa (exp_of_spl (r s. ''r_cnt'')) [+] 
                    (elrl [val_c (CHR ''1'')]))))
                ] END IF),
              ('''': (clhs_v (lhs_v (var_of_vl (v v.''v_qcorr'')))) := (rhs_e (bexpl (exp_nth (exp_of_vl  (v v.''v_x'')) 
                (en 64)) [xor] (exp_nth (exp_of_spl (divi s.''divi_y'')) (en 32)))))
              ]),
            (WHEN [elrl [(val_c (CHR ''1'')),(val_c (CHR ''0'')),(val_c (CHR ''0''))]] => [
              ('''': (clhs_v (lhs_v vaddin1)) := (rhs_e (exp_sl (exp_of_spl (r s.''r_x'')) (en 32) (en 64)))),
              ('''': (clhs_v (lhs_v (var_of_vl (v v.''v_state'')))) := (rhs_e (elrl [(val_c (CHR ''1'')),
                (val_c (CHR ''0'')),(val_c (CHR ''1''))])))
              ])
            ] WHEN OTHERS => [
              ('''': (clhs_v (lhs_v vaddin1)) := (rhs_e (bexpa (bexpa (exp_trl (uexp [not] (exp_nth (exp_of_spl (r s.''r_x'')) 
                (en 31)))) [&] (exp_sl (exp_of_spl (r s.''r_x'')) (en 0) (en 30))) [&] (elrl [val_c (CHR ''1'')])))), 
              ('''': (clhs_v (lhs_v vaddin2)) := (OTHERS => (el (CHR ''0'')))),
              ('''': (clhs_v (lhs_va vaddin2 ((en 0) DOWNTO (en 0)))) := (rhs_e (elrl [(val_c (CHR ''1''))]))),
              ('''': (clhs_v (lhs_v vaddsub)) := (rhs_e (uexp [not] (exp_of_spl (r s.''r_neg''))))),
              ('''': IF (bexpl (bexpl (bexpr (exp_of_spl (r s.''r_qcorr'')) [=] (el (CHR ''1''))) [or] 
                (bexpr (exp_of_spl (r s.''r_zero'')) [=] (el (CHR ''1'')))) [and] 
                (bexpr (exp_of_spl (r s.''r_zero2'')) [=] (el (CHR ''0'')))) THEN [
                ('''': IF (bexpl (bexpr (exp_of_spl (r s.''r_zero'')) [=] (el (CHR ''1''))) [and] 
                  (bexpl (bexpr (exp_of_spl (r s.''r_qcorr'')) [=] (el (CHR ''0''))) [and] 
                  (bexpr (exp_of_spl (r s.''r_zcorr'')) [=] (el (CHR ''1''))))) THEN [
                  ('''': (clhs_v (lhs_v vaddsub)) := (rhs_e (exp_of_spl (r s.''r_neg'')))),
                  ('''': (clhs_v (lhs_v (var_of_vl (v v.''v_qzero'')))) := (rhs_e (el (CHR ''0''))))
                ] [] ELSE [] END IF),
                ('''': (clhs_v (lhs_va (var_of_vl (v v.''v_x'')) ((en 64) DOWNTO (en 32)))) := (rhs_e (exp_sig addout)))
              ] [] ELSE [
                ('''': (clhs_v (lhs_va (var_of_vl (v v.''v_x'')) ((en 64) DOWNTO (en 32)))) := (rhs_e (exp_var vaddin1))),
                ('''': (clhs_v (lhs_v (var_of_vl (v v.''v_qzero'')))) := (rhs_e (el (CHR ''0''))))
              ] END IF),
              ('''': IF (bexpr (exp_of_spl (r s.''r_ovf'')) [=] (el (CHR ''1''))) THEN [
                ('''': (clhs_v (lhs_v (var_of_vl (v v.''v_qzero'')))) := (rhs_e (el (CHR ''0'')))),
                ('''': (clhs_v (lhs_va (var_of_vl (v v.''v_x'')) ((en 63) DOWNTO (en 32)))) := (OTHERS => (el (CHR ''1'')))),
                ('''': IF (bexpr (exp_of_spl (divi s.''divi_signed'')) [=] (el (CHR ''1''))) THEN [
                  ('''': IF (bexpr (exp_of_spl (r s.''r_neg'')) [=] (el (CHR ''1''))) THEN [
                    ('''': (clhs_v (lhs_va (var_of_vl (v v.''v_x'')) ((en 62) DOWNTO (en 32)))) := (OTHERS => (el (CHR ''0''))))
                  ] [] ELSE [
                    ('''': (clhs_v (lhs_va (var_of_vl (v v.''v_x'')) ((en 63) DOWNTO (en 63)))) := (rhs_e (elrl [val_c (CHR ''0'')])))
                  ] END IF)
                ] [] ELSE [] END IF)
              ] [] ELSE [] END IF),
              ('''': (clhs_v (lhs_v vready)) := (rhs_e (el (CHR ''1'')))),
              ('''': (clhs_v (lhs_v (var_of_vl (v v.''v_state'')))) := (rhs_e (elrl [(val_c (CHR ''0'')),
                (val_c (CHR ''0'')),(val_c (CHR ''0''))])))
            ] END CASE),

          ('''': (clhs_sp (lhs_s (sp_of_spl (divo s.''divo_icc'')))) <= (rhs_e (bexpa (bexpa (bexpa (exp_trl (exp_nth 
            (exp_of_spl (r s.''r_x'')) (en 63))) [&] (exp_trl (exp_of_spl (r s.''r_qzero'')))) [&] 
            (exp_trl (exp_of_spl (r s.''r_ovf'')))) [&] (elrl [val_c (CHR ''0'')])))), 
          ('''': IF (bexpr (exp_of_spl (divi s.''divi_flush'')) [=] (el (CHR ''1''))) THEN [
            ('''': (clhs_v (lhs_v (var_of_vl (v v.''v_state'')))) := (rhs_e (elrl [(val_c (CHR ''0'')),
                (val_c (CHR ''0'')),(val_c (CHR ''0''))])))
          ] [] ELSE [] END IF),
          ('''': IF (bexpl (uexp [not] (exp_var async_reset)) [and] (bexpl (uexp [not] 
            (exp_var reset_all)) [and] (bexpr (exp_prt rst) [=] (eul (CHR ''0''))))) THEN [
            ('''': (clhs_v (lhs_v (var_of_vl (v v.''v_state'')))) := (rhs_e (exp_of_vl (rres v.''rres_state'')))),
            ('''': (clhs_v (lhs_v (var_of_vl (v v.''v_cnt'')))) := (rhs_e (exp_of_vl (rres v.''rres_cnt''))))
          ] [] ELSE [] END IF),
          ('''': (clhs_spr rin) <= (rhs_e (exp_r (rhsl_of_vl v)))),
          ('''': (clhs_sp (lhs_s (sp_of_spl (divo s.''divo_ready'')))) <= (rhs_e (exp_var vready))),
          ('''': (clhs_sp (lhs_s (sp_of_spl (divo s.''divo_nready'')))) <= (rhs_e (exp_var vnready))),
          ('''': (clhs_sp (lhs_sa (sp_of_spl (divo s.''divo_result'')) ((en 31) DOWNTO (en 0)))) <= 
            (rhs_e (exp_sl (exp_of_spl (r s.''r_x'')) (en 32) (en 63)))),
          ('''': (clhs_sp (lhs_s (sp_s addin1))) <= (rhs_e (exp_var vaddin1))),
          ('''': (clhs_sp (lhs_s (sp_s addin2))) <= (rhs_e (exp_var vaddin2))),
          ('''': (clhs_sp (lhs_s (sp_s addsub))) <= (rhs_e (exp_var vaddsub)))
        ] END PROCESS),
        (''divadd'': PROCESS ([sp_s addin1, sp_s addin2, sp_s addsub]) BEGIN [
          ('''': IF (bexpr (exp_sig addsub) [=] (el (CHR ''1''))) THEN [
            ('''': (clhs_v (lhs_v b)) := (rhs_e (uexp [not] (exp_sig addin2))))
          ] [] ELSE [
            ('''': (clhs_v (lhs_v b)) := (rhs_e (exp_sig addin2)))
          ] END IF),
          ('''': (clhs_sp (lhs_s (sp_s addout))) <= (rhs_e (bexpa (bexpa (exp_sig addin1) [+] 
            (exp_var b)) [+] (exp_trl (exp_sig addsub)))))
        ] END PROCESS),
        (''syncrregs'': IF (uexp [not] (exp_var async_reset)) GENERATE BEGIN [
          (''reg'': PROCESS ([sp_p p_clk]) BEGIN [
            ('''': IF (bexpr (exp_prt p_clk) [=] (eul (CHR ''1''))) THEN [
              ('''': IF (bexpr (exp_prt holdn) [=] (eul (CHR ''1''))) THEN [
                ('''': (clhs_spr r) <= (rhs_e (exp_r (rhsl_of_spl rin))))
              ] [] ELSE [] END IF),
              ('''': IF (bexpr (exp_prt rst) [=] (eul (CHR ''0''))) THEN [
                ('''': IF (exp_var reset_all) THEN [
                  ('''': (clhs_spr r) <= (rhs_e (exp_r (rhsl_of_vl rres))))
                ] [] ELSE [
                  ('''': (clhs_sp (lhs_s (sp_of_spl (r s.''r_state'')))) <= (rhs_e (exp_of_vl (rres v.''rres_state'')))),
                  ('''': (clhs_sp (lhs_s (sp_of_spl (r s.''r_cnt'')))) <= (rhs_e (exp_of_vl (rres v.''rres_cnt''))))
                ] END IF)
              ] [] ELSE [] END IF)
            ] [] ELSE [] END IF)
          ] END PROCESS)
        ] END GENERATE),
        (''asyncrregs'': IF (exp_var async_reset) GENERATE BEGIN [
          (''reg'': PROCESS ([sp_p p_clk, sp_s arst]) BEGIN [
            ('''': IF (bexpr (exp_sig arst) [=] (eul (CHR ''0''))) THEN [
              ('''': (clhs_spr r) <= (rhs_e (exp_r (rhsl_of_vl rres))))
            ] [
              (ELSIF (bexpr (exp_prt p_clk) [=] (eul (CHR ''1'')))  THEN [
                ('''': IF (bexpr (exp_prt holdn) [=] (eul (CHR ''1''))) THEN [
                  ('''': (clhs_spr r) <= (rhs_e (exp_r (rhsl_of_spl rin))))
                ] [] ELSE [] END IF)
              ])
            ] ELSE [] END IF)
          ] END PROCESS)
        ] END GENERATE)
      ]
  in
  (env, resfn, cst_list,[])
"

export_code div32 simulation init_state trans_vhdl_desc_complex in OCaml
module_name vhdl_div32 file vhdl_div32

end