(*
 * Copyright 2016, NTU
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * Author: Zhe Hou.
 *)

theory VHDL_Types
imports Main VHDL_Syntax
begin

text {* This file defines the minimal types in VHDL 
and their operations. *}

text {* The following is taken from Section 4.4 of [1],
it defines the well-formedness of basic types. *}
definition vhdl_boolean:: "type" where
"vhdl_boolean \<equiv> subtype ''vhdl_boolean'' emptype"

definition vhdl_bit:: "type" where
"vhdl_bit \<equiv> subtype ''vhdl_bit'' emptype"

definition vhdl_character:: "type" where
"vhdl_character \<equiv> subtype ''vhdl_character'' emptype"

definition vhdl_integer:: "type" where
"vhdl_integer \<equiv> subtype ''vhdl_integer'' emptype"

definition vhdl_positive:: "type" where
"vhdl_positive \<equiv> subtype ''vhdl_positive''  vhdl_integer"

definition vhdl_natural:: "type" where
"vhdl_natural \<equiv> subtype ''vhdl_natural''  vhdl_integer"

definition vhdl_real:: "type" where
"vhdl_real \<equiv> subtype ''vhdl_real'' emptype"

definition vhdl_time:: "type" where
"vhdl_time \<equiv> subtype ''vhdl_time'' emptype"

text {* infinity is a speical value for timeout. *}
definition infinity:: "val" where
"infinity \<equiv> val_i 2147483648"

text {* We don't consider severity_levels. *}

definition minimal_types:: "type set" where
"minimal_types \<equiv> {vhdl_boolean, vhdl_bit, vhdl_character, vhdl_integer, 
  vhdl_real, vhdl_time, vhdl_positive, vhdl_natural}"

definition vhdl_string:: "type" where
"vhdl_string \<equiv> subtype ''vhdl_string'' vhdl_character"

definition vhdl_bitstr:: "type" where
"vhdl_bitstr \<equiv> subtype ''vhdl_bitstr'' vhdl_character"

definition vhdl_boolstr:: "type" where
"vhdl_boolstr \<equiv> subtype ''vhdl_boolstr'' vhdl_boolean"

text {* We support the widely used types such as 
std_logic, std_ulogic, std_logic_vector, and std_ulogic_vector. 
We treat the values of these types the same way as vhdl_character,
i.e., the values are: 
val_c (CHR ''U''),
val_c (CHR ''X''),
val_c (CHR ''0''),
val_c (CHR ''1''),
val_c (CHR ''Z''),
val_c (CHR ''W''),
val_c (CHR ''L''),
val_c (CHR ''H''),
val_c (CHR ''-'').*}

definition vhdl_std_ulogic:: "type" where
"vhdl_std_ulogic \<equiv> subtype ''vhdl_std_ulogic'' emptype"

definition vhdl_std_logic:: "type" where
"vhdl_std_logic \<equiv> subtype ''vhdl_std_logic'' vhdl_std_ulogic"

definition vhdl_std_ulogic_vector:: "type" where
"vhdl_std_ulogic_vector \<equiv> subtype ''vhdl_std_ulogic_vector'' vhdl_std_ulogic"

definition vhdl_std_logic_vector:: "type" where
"vhdl_std_logic_vector \<equiv> subtype ''vhdl_std_logic_vector'' vhdl_std_logic"

definition vhdl_array:: "type" where
"vhdl_array \<equiv> subtype ''vhdl_array'' emptype"

text {* We define logical operations over std_logic values explicitly below. 
The definitions below are based on std_logic_1164.vhd. *}

definition std_logic_not:: "char \<Rightarrow> char" where
"std_logic_not c \<equiv>
  case c of
   (CHR ''U'') \<Rightarrow> (CHR ''U'')
  |(CHR ''X'') \<Rightarrow> (CHR ''X'')
  |(CHR ''0'') \<Rightarrow> (CHR ''1'')
  |(CHR ''1'') \<Rightarrow> (CHR ''0'')
  |(CHR ''Z'') \<Rightarrow> (CHR ''X'')
  |(CHR ''W'') \<Rightarrow> (CHR ''X'')
  |(CHR ''L'') \<Rightarrow> (CHR ''1'')
  |(CHR ''H'') \<Rightarrow> (CHR ''0'')
  |(CHR ''-'') \<Rightarrow> (CHR ''X'')
  |_ \<Rightarrow> c
"

definition std_logic_and:: "char \<Rightarrow> char \<Rightarrow> char" where
"std_logic_and c1 c2 \<equiv>
  case c1 of
  (CHR ''U'') \<Rightarrow> (
    case c2 of 
     (CHR ''U'') \<Rightarrow> (CHR ''U'')
    |(CHR ''X'') \<Rightarrow> (CHR ''U'')
    |(CHR ''0'') \<Rightarrow> (CHR ''0'')
    |(CHR ''1'') \<Rightarrow> (CHR ''U'')
    |(CHR ''Z'') \<Rightarrow> (CHR ''U'')
    |(CHR ''W'') \<Rightarrow> (CHR ''U'')
    |(CHR ''L'') \<Rightarrow> (CHR ''0'')
    |(CHR ''H'') \<Rightarrow> (CHR ''U'')
    |(CHR ''-'') \<Rightarrow> (CHR ''U'')
    |_ \<Rightarrow> c1)
  |(CHR ''X'') \<Rightarrow> (
    case c2 of 
     (CHR ''U'') \<Rightarrow> (CHR ''U'')
    |(CHR ''X'') \<Rightarrow> (CHR ''X'')
    |(CHR ''0'') \<Rightarrow> (CHR ''0'')
    |(CHR ''1'') \<Rightarrow> (CHR ''X'')
    |(CHR ''Z'') \<Rightarrow> (CHR ''X'')
    |(CHR ''W'') \<Rightarrow> (CHR ''X'')
    |(CHR ''L'') \<Rightarrow> (CHR ''0'')
    |(CHR ''H'') \<Rightarrow> (CHR ''X'')
    |(CHR ''-'') \<Rightarrow> (CHR ''X'')
    |_ \<Rightarrow> c1)
  |(CHR ''0'') \<Rightarrow> (
    case c2 of 
     (CHR ''U'') \<Rightarrow> (CHR ''0'')
    |(CHR ''X'') \<Rightarrow> (CHR ''0'')
    |(CHR ''0'') \<Rightarrow> (CHR ''0'')
    |(CHR ''1'') \<Rightarrow> (CHR ''0'')
    |(CHR ''Z'') \<Rightarrow> (CHR ''0'')
    |(CHR ''W'') \<Rightarrow> (CHR ''0'')
    |(CHR ''L'') \<Rightarrow> (CHR ''0'')
    |(CHR ''H'') \<Rightarrow> (CHR ''0'')
    |(CHR ''-'') \<Rightarrow> (CHR ''0'')
    |_ \<Rightarrow> c1)
  |(CHR ''1'') \<Rightarrow> (
    case c2 of 
     (CHR ''U'') \<Rightarrow> (CHR ''U'')
    |(CHR ''X'') \<Rightarrow> (CHR ''X'')
    |(CHR ''0'') \<Rightarrow> (CHR ''0'')
    |(CHR ''1'') \<Rightarrow> (CHR ''1'')
    |(CHR ''Z'') \<Rightarrow> (CHR ''X'')
    |(CHR ''W'') \<Rightarrow> (CHR ''X'')
    |(CHR ''L'') \<Rightarrow> (CHR ''0'')
    |(CHR ''H'') \<Rightarrow> (CHR ''1'')
    |(CHR ''-'') \<Rightarrow> (CHR ''X'')
    |_ \<Rightarrow> c1)
  |(CHR ''Z'') \<Rightarrow> (
    case c2 of 
     (CHR ''U'') \<Rightarrow> (CHR ''U'')
    |(CHR ''X'') \<Rightarrow> (CHR ''X'')
    |(CHR ''0'') \<Rightarrow> (CHR ''0'')
    |(CHR ''1'') \<Rightarrow> (CHR ''X'')
    |(CHR ''Z'') \<Rightarrow> (CHR ''X'')
    |(CHR ''W'') \<Rightarrow> (CHR ''X'')
    |(CHR ''L'') \<Rightarrow> (CHR ''0'')
    |(CHR ''H'') \<Rightarrow> (CHR ''X'')
    |(CHR ''-'') \<Rightarrow> (CHR ''X'')
    |_ \<Rightarrow> c1)
  |(CHR ''W'') \<Rightarrow> (
    case c2 of 
     (CHR ''U'') \<Rightarrow> (CHR ''U'')
    |(CHR ''X'') \<Rightarrow> (CHR ''X'')
    |(CHR ''0'') \<Rightarrow> (CHR ''0'')
    |(CHR ''1'') \<Rightarrow> (CHR ''X'')
    |(CHR ''Z'') \<Rightarrow> (CHR ''X'')
    |(CHR ''W'') \<Rightarrow> (CHR ''X'')
    |(CHR ''L'') \<Rightarrow> (CHR ''0'')
    |(CHR ''H'') \<Rightarrow> (CHR ''X'')
    |(CHR ''-'') \<Rightarrow> (CHR ''X'')
    |_ \<Rightarrow> c1)
  |(CHR ''L'') \<Rightarrow> (
    case c2 of 
     (CHR ''U'') \<Rightarrow> (CHR ''0'')
    |(CHR ''X'') \<Rightarrow> (CHR ''0'')
    |(CHR ''0'') \<Rightarrow> (CHR ''0'')
    |(CHR ''1'') \<Rightarrow> (CHR ''0'')
    |(CHR ''Z'') \<Rightarrow> (CHR ''0'')
    |(CHR ''W'') \<Rightarrow> (CHR ''0'')
    |(CHR ''L'') \<Rightarrow> (CHR ''0'')
    |(CHR ''H'') \<Rightarrow> (CHR ''0'')
    |(CHR ''-'') \<Rightarrow> (CHR ''0'')
    |_ \<Rightarrow> c1)
  |(CHR ''H'') \<Rightarrow> (
    case c2 of 
     (CHR ''U'') \<Rightarrow> (CHR ''U'')
    |(CHR ''X'') \<Rightarrow> (CHR ''X'')
    |(CHR ''0'') \<Rightarrow> (CHR ''0'')
    |(CHR ''1'') \<Rightarrow> (CHR ''1'')
    |(CHR ''Z'') \<Rightarrow> (CHR ''X'')
    |(CHR ''W'') \<Rightarrow> (CHR ''X'')
    |(CHR ''L'') \<Rightarrow> (CHR ''0'')
    |(CHR ''H'') \<Rightarrow> (CHR ''1'')
    |(CHR ''-'') \<Rightarrow> (CHR ''X'')
    |_ \<Rightarrow> c1)
  |(CHR ''-'') \<Rightarrow> (
    case c2 of 
     (CHR ''U'') \<Rightarrow> (CHR ''U'')
    |(CHR ''X'') \<Rightarrow> (CHR ''X'')
    |(CHR ''0'') \<Rightarrow> (CHR ''0'')
    |(CHR ''1'') \<Rightarrow> (CHR ''X'')
    |(CHR ''Z'') \<Rightarrow> (CHR ''X'')
    |(CHR ''W'') \<Rightarrow> (CHR ''X'')
    |(CHR ''L'') \<Rightarrow> (CHR ''0'')
    |(CHR ''H'') \<Rightarrow> (CHR ''X'')
    |(CHR ''-'') \<Rightarrow> (CHR ''X'')
    |_ \<Rightarrow> c1)
  |_ \<Rightarrow> c1
"

definition std_logic_or:: "char \<Rightarrow> char \<Rightarrow> char" where
"std_logic_or c1 c2 \<equiv>
  case c1 of
  (CHR ''U'') \<Rightarrow> (
    case c2 of 
     (CHR ''U'') \<Rightarrow> (CHR ''U'')
    |(CHR ''X'') \<Rightarrow> (CHR ''U'')
    |(CHR ''0'') \<Rightarrow> (CHR ''U'')
    |(CHR ''1'') \<Rightarrow> (CHR ''1'')
    |(CHR ''Z'') \<Rightarrow> (CHR ''U'')
    |(CHR ''W'') \<Rightarrow> (CHR ''U'')
    |(CHR ''L'') \<Rightarrow> (CHR ''U'')
    |(CHR ''H'') \<Rightarrow> (CHR ''1'')
    |(CHR ''-'') \<Rightarrow> (CHR ''U'')
    |_ \<Rightarrow> c1)
  |(CHR ''X'') \<Rightarrow> (
    case c2 of 
     (CHR ''U'') \<Rightarrow> (CHR ''U'')
    |(CHR ''X'') \<Rightarrow> (CHR ''X'')
    |(CHR ''0'') \<Rightarrow> (CHR ''X'')
    |(CHR ''1'') \<Rightarrow> (CHR ''1'')
    |(CHR ''Z'') \<Rightarrow> (CHR ''X'')
    |(CHR ''W'') \<Rightarrow> (CHR ''X'')
    |(CHR ''L'') \<Rightarrow> (CHR ''X'')
    |(CHR ''H'') \<Rightarrow> (CHR ''1'')
    |(CHR ''-'') \<Rightarrow> (CHR ''X'')
    |_ \<Rightarrow> c1)
  |(CHR ''0'') \<Rightarrow> (
    case c2 of 
     (CHR ''U'') \<Rightarrow> (CHR ''U'')
    |(CHR ''X'') \<Rightarrow> (CHR ''X'')
    |(CHR ''0'') \<Rightarrow> (CHR ''0'')
    |(CHR ''1'') \<Rightarrow> (CHR ''1'')
    |(CHR ''Z'') \<Rightarrow> (CHR ''X'')
    |(CHR ''W'') \<Rightarrow> (CHR ''X'')
    |(CHR ''L'') \<Rightarrow> (CHR ''0'')
    |(CHR ''H'') \<Rightarrow> (CHR ''1'')
    |(CHR ''-'') \<Rightarrow> (CHR ''X'')
    |_ \<Rightarrow> c1)
  |(CHR ''1'') \<Rightarrow> (
    case c2 of 
     (CHR ''U'') \<Rightarrow> (CHR ''1'')
    |(CHR ''X'') \<Rightarrow> (CHR ''1'')
    |(CHR ''0'') \<Rightarrow> (CHR ''1'')
    |(CHR ''1'') \<Rightarrow> (CHR ''1'')
    |(CHR ''Z'') \<Rightarrow> (CHR ''1'')
    |(CHR ''W'') \<Rightarrow> (CHR ''1'')
    |(CHR ''L'') \<Rightarrow> (CHR ''1'')
    |(CHR ''H'') \<Rightarrow> (CHR ''1'')
    |(CHR ''-'') \<Rightarrow> (CHR ''1'')
    |_ \<Rightarrow> c1)
  |(CHR ''Z'') \<Rightarrow> (
    case c2 of 
     (CHR ''U'') \<Rightarrow> (CHR ''U'')
    |(CHR ''X'') \<Rightarrow> (CHR ''X'')
    |(CHR ''0'') \<Rightarrow> (CHR ''X'')
    |(CHR ''1'') \<Rightarrow> (CHR ''1'')
    |(CHR ''Z'') \<Rightarrow> (CHR ''X'')
    |(CHR ''W'') \<Rightarrow> (CHR ''X'')
    |(CHR ''L'') \<Rightarrow> (CHR ''X'')
    |(CHR ''H'') \<Rightarrow> (CHR ''1'')
    |(CHR ''-'') \<Rightarrow> (CHR ''X'')
    |_ \<Rightarrow> c1)
  |(CHR ''W'') \<Rightarrow> (
    case c2 of 
     (CHR ''U'') \<Rightarrow> (CHR ''U'')
    |(CHR ''X'') \<Rightarrow> (CHR ''X'')
    |(CHR ''0'') \<Rightarrow> (CHR ''X'')
    |(CHR ''1'') \<Rightarrow> (CHR ''1'')
    |(CHR ''Z'') \<Rightarrow> (CHR ''X'')
    |(CHR ''W'') \<Rightarrow> (CHR ''X'')
    |(CHR ''L'') \<Rightarrow> (CHR ''X'')
    |(CHR ''H'') \<Rightarrow> (CHR ''1'')
    |(CHR ''-'') \<Rightarrow> (CHR ''X'')
    |_ \<Rightarrow> c1)
  |(CHR ''L'') \<Rightarrow> (
    case c2 of 
     (CHR ''U'') \<Rightarrow> (CHR ''U'')
    |(CHR ''X'') \<Rightarrow> (CHR ''X'')
    |(CHR ''0'') \<Rightarrow> (CHR ''0'')
    |(CHR ''1'') \<Rightarrow> (CHR ''1'')
    |(CHR ''Z'') \<Rightarrow> (CHR ''X'')
    |(CHR ''W'') \<Rightarrow> (CHR ''X'')
    |(CHR ''L'') \<Rightarrow> (CHR ''0'')
    |(CHR ''H'') \<Rightarrow> (CHR ''1'')
    |(CHR ''-'') \<Rightarrow> (CHR ''X'')
    |_ \<Rightarrow> c1)
  |(CHR ''H'') \<Rightarrow> (
    case c2 of 
     (CHR ''U'') \<Rightarrow> (CHR ''1'')
    |(CHR ''X'') \<Rightarrow> (CHR ''1'')
    |(CHR ''0'') \<Rightarrow> (CHR ''1'')
    |(CHR ''1'') \<Rightarrow> (CHR ''1'')
    |(CHR ''Z'') \<Rightarrow> (CHR ''1'')
    |(CHR ''W'') \<Rightarrow> (CHR ''1'')
    |(CHR ''L'') \<Rightarrow> (CHR ''1'')
    |(CHR ''H'') \<Rightarrow> (CHR ''1'')
    |(CHR ''-'') \<Rightarrow> (CHR ''1'')
    |_ \<Rightarrow> c1)
  |(CHR ''-'') \<Rightarrow> (
    case c2 of 
     (CHR ''U'') \<Rightarrow> (CHR ''U'')
    |(CHR ''X'') \<Rightarrow> (CHR ''X'')
    |(CHR ''0'') \<Rightarrow> (CHR ''X'')
    |(CHR ''1'') \<Rightarrow> (CHR ''1'')
    |(CHR ''Z'') \<Rightarrow> (CHR ''X'')
    |(CHR ''W'') \<Rightarrow> (CHR ''X'')
    |(CHR ''L'') \<Rightarrow> (CHR ''X'')
    |(CHR ''H'') \<Rightarrow> (CHR ''1'')
    |(CHR ''-'') \<Rightarrow> (CHR ''X'')
    |_ \<Rightarrow> c1)
  |_ \<Rightarrow> c1
"

definition std_logic_xor:: "char \<Rightarrow> char \<Rightarrow> char" where
"std_logic_xor c1 c2 \<equiv>
  case c1 of
  (CHR ''U'') \<Rightarrow> (
    case c2 of 
     (CHR ''U'') \<Rightarrow> (CHR ''U'')
    |(CHR ''X'') \<Rightarrow> (CHR ''U'')
    |(CHR ''0'') \<Rightarrow> (CHR ''U'')
    |(CHR ''1'') \<Rightarrow> (CHR ''U'')
    |(CHR ''Z'') \<Rightarrow> (CHR ''U'')
    |(CHR ''W'') \<Rightarrow> (CHR ''U'')
    |(CHR ''L'') \<Rightarrow> (CHR ''U'')
    |(CHR ''H'') \<Rightarrow> (CHR ''U'')
    |(CHR ''-'') \<Rightarrow> (CHR ''U'')
    |_ \<Rightarrow> c1)
  |(CHR ''X'') \<Rightarrow> (
    case c2 of 
     (CHR ''U'') \<Rightarrow> (CHR ''U'')
    |(CHR ''X'') \<Rightarrow> (CHR ''X'')
    |(CHR ''0'') \<Rightarrow> (CHR ''X'')
    |(CHR ''1'') \<Rightarrow> (CHR ''X'')
    |(CHR ''Z'') \<Rightarrow> (CHR ''X'')
    |(CHR ''W'') \<Rightarrow> (CHR ''X'')
    |(CHR ''L'') \<Rightarrow> (CHR ''X'')
    |(CHR ''H'') \<Rightarrow> (CHR ''X'')
    |(CHR ''-'') \<Rightarrow> (CHR ''X'')
    |_ \<Rightarrow> c1)
  |(CHR ''0'') \<Rightarrow> (
    case c2 of 
     (CHR ''U'') \<Rightarrow> (CHR ''U'')
    |(CHR ''X'') \<Rightarrow> (CHR ''X'')
    |(CHR ''0'') \<Rightarrow> (CHR ''0'')
    |(CHR ''1'') \<Rightarrow> (CHR ''1'')
    |(CHR ''Z'') \<Rightarrow> (CHR ''X'')
    |(CHR ''W'') \<Rightarrow> (CHR ''X'')
    |(CHR ''L'') \<Rightarrow> (CHR ''0'')
    |(CHR ''H'') \<Rightarrow> (CHR ''1'')
    |(CHR ''-'') \<Rightarrow> (CHR ''X'')
    |_ \<Rightarrow> c1)
  |(CHR ''1'') \<Rightarrow> (
    case c2 of 
     (CHR ''U'') \<Rightarrow> (CHR ''U'')
    |(CHR ''X'') \<Rightarrow> (CHR ''X'')
    |(CHR ''0'') \<Rightarrow> (CHR ''1'')
    |(CHR ''1'') \<Rightarrow> (CHR ''0'')
    |(CHR ''Z'') \<Rightarrow> (CHR ''X'')
    |(CHR ''W'') \<Rightarrow> (CHR ''X'')
    |(CHR ''L'') \<Rightarrow> (CHR ''1'')
    |(CHR ''H'') \<Rightarrow> (CHR ''0'')
    |(CHR ''-'') \<Rightarrow> (CHR ''X'')
    |_ \<Rightarrow> c1)
  |(CHR ''Z'') \<Rightarrow> (
    case c2 of 
     (CHR ''U'') \<Rightarrow> (CHR ''U'')
    |(CHR ''X'') \<Rightarrow> (CHR ''X'')
    |(CHR ''0'') \<Rightarrow> (CHR ''X'')
    |(CHR ''1'') \<Rightarrow> (CHR ''X'')
    |(CHR ''Z'') \<Rightarrow> (CHR ''X'')
    |(CHR ''W'') \<Rightarrow> (CHR ''X'')
    |(CHR ''L'') \<Rightarrow> (CHR ''X'')
    |(CHR ''H'') \<Rightarrow> (CHR ''X'')
    |(CHR ''-'') \<Rightarrow> (CHR ''X'')
    |_ \<Rightarrow> c1)
  |(CHR ''W'') \<Rightarrow> (
    case c2 of 
     (CHR ''U'') \<Rightarrow> (CHR ''U'')
    |(CHR ''X'') \<Rightarrow> (CHR ''X'')
    |(CHR ''0'') \<Rightarrow> (CHR ''X'')
    |(CHR ''1'') \<Rightarrow> (CHR ''X'')
    |(CHR ''Z'') \<Rightarrow> (CHR ''X'')
    |(CHR ''W'') \<Rightarrow> (CHR ''X'')
    |(CHR ''L'') \<Rightarrow> (CHR ''X'')
    |(CHR ''H'') \<Rightarrow> (CHR ''X'')
    |(CHR ''-'') \<Rightarrow> (CHR ''X'')
    |_ \<Rightarrow> c1)
  |(CHR ''L'') \<Rightarrow> (
    case c2 of 
     (CHR ''U'') \<Rightarrow> (CHR ''U'')
    |(CHR ''X'') \<Rightarrow> (CHR ''X'')
    |(CHR ''0'') \<Rightarrow> (CHR ''0'')
    |(CHR ''1'') \<Rightarrow> (CHR ''1'')
    |(CHR ''Z'') \<Rightarrow> (CHR ''X'')
    |(CHR ''W'') \<Rightarrow> (CHR ''X'')
    |(CHR ''L'') \<Rightarrow> (CHR ''0'')
    |(CHR ''H'') \<Rightarrow> (CHR ''1'')
    |(CHR ''-'') \<Rightarrow> (CHR ''X'')
    |_ \<Rightarrow> c1)
  |(CHR ''H'') \<Rightarrow> (
    case c2 of 
     (CHR ''U'') \<Rightarrow> (CHR ''U'')
    |(CHR ''X'') \<Rightarrow> (CHR ''X'')
    |(CHR ''0'') \<Rightarrow> (CHR ''1'')
    |(CHR ''1'') \<Rightarrow> (CHR ''0'')
    |(CHR ''Z'') \<Rightarrow> (CHR ''X'')
    |(CHR ''W'') \<Rightarrow> (CHR ''X'')
    |(CHR ''L'') \<Rightarrow> (CHR ''1'')
    |(CHR ''H'') \<Rightarrow> (CHR ''0'')
    |(CHR ''-'') \<Rightarrow> (CHR ''X'')
    |_ \<Rightarrow> c1)
  |(CHR ''-'') \<Rightarrow> (
    case c2 of 
     (CHR ''U'') \<Rightarrow> (CHR ''U'')
    |(CHR ''X'') \<Rightarrow> (CHR ''X'')
    |(CHR ''0'') \<Rightarrow> (CHR ''X'')
    |(CHR ''1'') \<Rightarrow> (CHR ''X'')
    |(CHR ''Z'') \<Rightarrow> (CHR ''X'')
    |(CHR ''W'') \<Rightarrow> (CHR ''X'')
    |(CHR ''L'') \<Rightarrow> (CHR ''X'')
    |(CHR ''H'') \<Rightarrow> (CHR ''X'')
    |(CHR ''-'') \<Rightarrow> (CHR ''X'')
    |_ \<Rightarrow> c1)
  |_ \<Rightarrow> c1
"

definition std_logic_nand:: "char \<Rightarrow> char \<Rightarrow> char" where
"std_logic_nand c1 c2 \<equiv> std_logic_not (std_logic_and c1 c2)"

definition std_logic_nor:: "char \<Rightarrow> char \<Rightarrow> char" where
"std_logic_nor c1 c2 \<equiv> std_logic_not (std_logic_or c1 c2)"

definition std_logic_xnor:: "char \<Rightarrow> char \<Rightarrow> char" where
"std_logic_xnor c1 c2 \<equiv> std_logic_or (std_logic_and c1 c2) 
                                     (std_logic_and (std_logic_not c1) (std_logic_not c2))"

text {* Logical operators not, and, nand, or, nor, xor, xnor on std_logic_vector
and std_ulogic_vector. The binary operators must operate on lists with the same length. 
These operations simply take each position in the list and invoke the corresponding 
functions on std_logic/std_ulogic. *}

primrec std_logic_vec_not:: "val list \<Rightarrow> val list" where
"std_logic_vec_not [] = []"
|"std_logic_vec_not (v#vx) = (
  case v of val_c c \<Rightarrow> (val_c (std_logic_not c))#(std_logic_vec_not vx))"

fun std_logic_vec_and:: "val list \<Rightarrow> val list \<Rightarrow> val list" where
"std_logic_vec_and [] [] = []"
|"std_logic_vec_and [] (v#vx) = []"
|"std_logic_vec_and (v#vx) [] = []"
|"std_logic_vec_and (v1#vx1) (v2#vx2) = (
  case (v1,v2) of (val_c c1, val_c c2) \<Rightarrow> 
    (val_c (std_logic_and c1 c2))#(std_logic_vec_and vx1 vx2))"

fun std_logic_vec_or:: "val list \<Rightarrow> val list \<Rightarrow> val list" where
"std_logic_vec_or [] [] = []"
|"std_logic_vec_or [] (v#vx) = []"
|"std_logic_vec_or (v#vx) [] = []"
|"std_logic_vec_or (v1#vx1) (v2#vx2) = (
  case (v1,v2) of (val_c c1, val_c c2) \<Rightarrow> 
    (val_c (std_logic_or c1 c2))#(std_logic_vec_or vx1 vx2))"

fun std_logic_vec_xor:: "val list \<Rightarrow> val list \<Rightarrow> val list" where
"std_logic_vec_xor [] [] = []"
|"std_logic_vec_xor [] (v#vx) = []"
|"std_logic_vec_xor (v#vx) [] = []"
|"std_logic_vec_xor (v1#vx1) (v2#vx2) = (
  case (v1,v2) of (val_c c1, val_c c2) \<Rightarrow> 
    (val_c (std_logic_xor c1 c2))#(std_logic_vec_xor vx1 vx2))"

fun std_logic_vec_nand:: "val list \<Rightarrow> val list \<Rightarrow> val list" where
"std_logic_vec_nand [] [] = []"
|"std_logic_vec_nand [] (v#vx) = []"
|"std_logic_vec_nand (v#vx) [] = []"
|"std_logic_vec_nand (v1#vx1) (v2#vx2) = (
  case (v1,v2) of (val_c c1, val_c c2) \<Rightarrow> 
    (val_c (std_logic_nand c1 c2))#(std_logic_vec_nand vx1 vx2))"

fun std_logic_vec_nor:: "val list \<Rightarrow> val list \<Rightarrow> val list" where
"std_logic_vec_nor [] [] = []"
|"std_logic_vec_nor [] (v#vx) = []"
|"std_logic_vec_nor (v#vx) [] = []"
|"std_logic_vec_nor (v1#vx1) (v2#vx2) = (
  case (v1,v2) of (val_c c1, val_c c2) \<Rightarrow> 
    (val_c (std_logic_nor c1 c2))#(std_logic_vec_nor vx1 vx2))"

fun std_logic_vec_xnor:: "val list \<Rightarrow> val list \<Rightarrow> val list" where
"std_logic_vec_xnor [] [] = []"
|"std_logic_vec_xnor [] (v#vx) = []"
|"std_logic_vec_xnor (v#vx) [] = []"
|"std_logic_vec_xnor (v1#vx1) (v2#vx2) = (
  case (v1,v2) of (val_c c1, val_c c2) \<Rightarrow> 
    (val_c (std_logic_xnor c1 c2))#(std_logic_vec_xnor vx1 vx2))"

text {* Addition for std_logic_vector and std_ulogic_vector. The length of the 
resultant list is the length of the larger list of input. *}

fun bin_add:: "val list \<Rightarrow> val list \<Rightarrow> nat \<Rightarrow> val list" where
"bin_add l1 l2 c = (
  if l1 = [] \<and> l2 = [] then [] 
  else if l1 = [] then (
    if (last l2) = (val_c (CHR ''0'')) then (
      if c = 1 then (bin_add [] (butlast l2) 0)@[val_c (CHR ''1'')]
      else l2
    )
    else (
      if c = 1 then (bin_add [] (butlast l2) 1)@[val_c (CHR ''0'')]
      else l2
    )
  )
  else if l2 = [] then (
    if (last l1) = (val_c (CHR ''0'')) then (
      if c = 1 then (bin_add [] (butlast l1) 0)@[val_c (CHR ''1'')]
      else l1
    )
    else (
      if c = 1 then (bin_add [] (butlast l1) 1)@[val_c (CHR ''0'')]
      else l1
    )
  )
  else (
    if (last l1) = (val_c (CHR ''0'')) \<and> (last l2) = (val_c (CHR ''0'')) then (
      if c = 1 then (bin_add (butlast l1) (butlast l2) 0)@[val_c (CHR ''1'')]
      else (bin_add (butlast l1) (butlast l2) 0)@[val_c (CHR ''0'')]
    )
    else if (last l1) = (val_c (CHR ''0'')) \<and> (last l2) = (val_c (CHR ''1'')) then (
      if c = 1 then (bin_add (butlast l1) (butlast l2) 1)@[val_c (CHR ''0'')]
      else (bin_add (butlast l1) (butlast l2) 0)@[val_c (CHR ''1'')]
    )
    else if (last l1) = (val_c (CHR ''1'')) \<and> (last l2) = (val_c (CHR ''0'')) then (
      if c = 1 then (bin_add (butlast l1) (butlast l2) 1)@[val_c (CHR ''0'')]
      else (bin_add (butlast l1) (butlast l2) 0)@[val_c (CHR ''1'')]
    )
    else (
      if c = 1 then (bin_add (butlast l1) (butlast l2) 1)@[val_c (CHR ''1'')]
      else (bin_add (butlast l1) (butlast l2) 1)@[val_c (CHR ''0'')]
    )
  )
)"

definition std_logic_vec_add:: "val list \<Rightarrow> val list \<Rightarrow> val list" where
"std_logic_vec_add l1 l2 \<equiv> bin_add l1 l2 0"

text {* Subtraction for std_logic_vector. The length of the resultant list 
is the length of the first input list. *}

fun bin_sub:: "val list \<Rightarrow> val list \<Rightarrow> nat \<Rightarrow> val list" where
"bin_sub l1 l2 c = (
  if l1 = [] then [] 
  else if l2 = [] then (
    if (last l1) = (val_c (CHR ''0'')) then (
      if c = 1 then (bin_sub [] (butlast l1) 1)@[val_c (CHR ''1'')]
      else l1
    )
    else (
      if c = 1 then (bin_sub [] (butlast l1) 0)@[val_c (CHR ''0'')]
      else l1
    )
  )
  else (
    if (last l1) = (val_c (CHR ''0'')) \<and> (last l2) = (val_c (CHR ''0'')) then (
      if c = 1 then (bin_sub (butlast l1) (butlast l2) 1)@[val_c (CHR ''1'')]
      else (bin_sub (butlast l1) (butlast l2) 0)@[val_c (CHR ''0'')]
    )
    else if (last l1) = (val_c (CHR ''0'')) \<and> (last l2) = (val_c (CHR ''1'')) then (
      if c = 1 then (bin_sub (butlast l1) (butlast l2) 1)@[val_c (CHR ''0'')]
      else (bin_sub (butlast l1) (butlast l2) 1)@[val_c (CHR ''1'')]
    )
    else if (last l1) = (val_c (CHR ''1'')) \<and> (last l2) = (val_c (CHR ''0'')) then (
      if c = 1 then (bin_sub (butlast l1) (butlast l2) 0)@[val_c (CHR ''0'')]
      else (bin_sub (butlast l1) (butlast l2) 0)@[val_c (CHR ''1'')]
    )
    else (
      if c = 1 then (bin_sub (butlast l1) (butlast l2) 1)@[val_c (CHR ''1'')]
      else (bin_sub (butlast l1) (butlast l2) 0)@[val_c (CHR ''0'')]
    )
  )
)"

definition std_logic_vec_sub:: "val list \<Rightarrow> val list \<Rightarrow> val list" where
"std_logic_vec_sub l1 l2 \<equiv> bin_sub l1 l2 0"

primrec shiftl1_bits:: "val list \<Rightarrow> val list" where
"shiftl1_bits [] = []"
|"shiftl1_bits (x # xs) = xs @[val_c (CHR ''0'')]"

primrec shiftr1_bits:: "val list \<Rightarrow> val list" where
"shiftr1_bits [] = []"
|"shiftr1_bits (x # xs) = [val_c (CHR ''0'')]@(butlast (x # xs))"

definition sll_bits:: "nat \<Rightarrow> val list \<Rightarrow> val list" where
"sll_bits n vl \<equiv> (shiftl1_bits ^^ n) vl"

definition srl_bits:: "nat \<Rightarrow> val list \<Rightarrow> val list" where
"srl_bits n vl \<equiv> (shiftr1_bits ^^ n) vl"

definition sla_bits:: "nat \<Rightarrow> val list \<Rightarrow> val list" where
"sla_bits \<equiv> sll_bits"

primrec shiftra1:: "'a list \<Rightarrow> 'a list" where
"shiftra1 [] = []"
|"shiftra1 (x # xs) = [x]@(butlast (x # xs))"

definition sra:: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"sra n l \<equiv> (shiftra1 ^^ n) l"

definition rol::"nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"rol n l \<equiv> rotate n l"

primrec rotater1:: "'a list \<Rightarrow> 'a list" where
"rotater1 [] = []"
|"rotater1 (x # xs) = [last (x # xs)]@(butlast (x # xs))"

definition ror:: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"ror n \<equiv> rotater1 ^^ n"

primrec shiftl1_bools:: "val list \<Rightarrow> val list" where
"shiftl1_bools [] = []"
|"shiftl1_bools (x # xs) = xs @[val_b False]"

primrec shiftr1_bools:: "val list \<Rightarrow> val list" where
"shiftr1_bools [] = []"
|"shiftr1_bools (x # xs) = [val_b False]@(butlast (x # xs))"

definition sll_bools:: "nat \<Rightarrow> val list \<Rightarrow> val list" where
"sll_bools n vl \<equiv> (shiftl1_bools ^^ n) vl"

definition srl_bools:: "nat \<Rightarrow> val list \<Rightarrow> val list" where
"srl_bools n vl \<equiv> (shiftr1_bools ^^ n) vl"

definition sla_bools:: "nat \<Rightarrow> val list \<Rightarrow> val list" where
"sla_bools \<equiv> sll_bools"

definition val_uop:: "type \<Rightarrow> uop \<Rightarrow> val option \<Rightarrow> val option" where
"val_uop t opr v \<equiv> 
  if opr = [-:] \<and> t \<in> {vhdl_integer, vhdl_time} then 
    case v of Some (val_i i) \<Rightarrow> Some (val_i (-i))
    | _ \<Rightarrow> None
  else if opr = [-:] \<and> t = vhdl_real then
    case v of Some (val_r r) \<Rightarrow> Some (val_r (-r))
    | _ \<Rightarrow> None
  else if opr = [-:] \<and> t \<in> {vhdl_positive, vhdl_natural} then
    case v of Some (val_i i) \<Rightarrow> None
    |_ \<Rightarrow> None
  else if opr = [+:] \<and> t \<in> {vhdl_integer, vhdl_real, vhdl_time,
    vhdl_positive, vhdl_natural} then v
  else if opr = [abs] \<and> t \<in> {vhdl_integer, vhdl_time} then
    case v of Some (val_i i) \<Rightarrow> Some (val_i (\<bar>i\<bar>))
    |_ \<Rightarrow> None
  else if opr = [abs] \<and> t = vhdl_real then
    case v of Some (val_r r) \<Rightarrow> Some (val_r (\<bar>r\<bar>))
    |_ \<Rightarrow> None
  else if opr = [abs] \<and> t \<in> {vhdl_positive, vhdl_natural} then v
  else if opr = [not] \<and> t = vhdl_boolean then
    case v of Some (val_b b) \<Rightarrow> Some (val_b (\<not> b))
    |_ \<Rightarrow> None
  else if opr = [not] \<and> t \<in> {vhdl_std_ulogic, vhdl_std_logic} then
    case v of Some (val_c c) \<Rightarrow> Some (val_c (std_logic_not c))
    |_ \<Rightarrow> None
  else if opr = [not] \<and> t \<in> {vhdl_std_ulogic_vector, vhdl_std_logic_vector} then
    case v of Some (val_list l) \<Rightarrow> Some (val_list (std_logic_vec_not l))
    |Some (val_rlist l) \<Rightarrow> Some (val_rlist (std_logic_vec_not l))
    |_ \<Rightarrow> None
  else None"

definition val_logical:: "type \<Rightarrow> lop \<Rightarrow> val option \<Rightarrow> val option \<Rightarrow> val option" where
"val_logical t opr v1 v2 \<equiv> 
  if opr = [and] \<and> t = vhdl_boolean then
    case (v1,v2) of ((Some (val_b b1)),(Some (val_b b2))) \<Rightarrow> 
      Some (val_b (b1 \<and> b2))
    |_ \<Rightarrow> None
  else if opr = [and] \<and> t \<in> {vhdl_std_ulogic, vhdl_std_logic} then
    case (v1,v2) of ((Some (val_c c1)),(Some (val_c c2))) \<Rightarrow> 
      Some (val_c (std_logic_and c1 c2))
    |_ \<Rightarrow> None
  else if opr = [and] \<and> t \<in> {vhdl_std_ulogic_vector, vhdl_std_logic_vector} then
    case (v1,v2) of ((Some (val_list l1)),(Some (val_list l2))) \<Rightarrow> 
      Some (val_list (std_logic_vec_and l1 l2))
    |((Some (val_rlist l1)),(Some (val_rlist l2))) \<Rightarrow> 
      Some (val_rlist (std_logic_vec_and l1 l2))
    |_ \<Rightarrow> None
  else if opr = [or] \<and> t = vhdl_boolean then
    case (v1,v2) of ((Some (val_b b1)),(Some (val_b b2))) \<Rightarrow> 
      Some (val_b (b1 \<or> b2))
    |_ \<Rightarrow> None
  else if opr = [or] \<and> t \<in> {vhdl_std_ulogic, vhdl_std_logic} then
    case (v1,v2) of ((Some (val_c c1)),(Some (val_c c2))) \<Rightarrow> 
      Some (val_c (std_logic_or c1 c2))
    |_ \<Rightarrow> None
  else if opr = [or] \<and> t \<in> {vhdl_std_ulogic_vector, vhdl_std_logic_vector} then
    case (v1,v2) of ((Some (val_list l1)),(Some (val_list l2))) \<Rightarrow> 
      Some (val_list (std_logic_vec_or l1 l2))
    |((Some (val_rlist l1)),(Some (val_rlist l2))) \<Rightarrow> 
      Some (val_rlist (std_logic_vec_or l1 l2))
    |_ \<Rightarrow> None
  else if opr = [nand] \<and> t = vhdl_boolean then
    case (v1,v2) of ((Some (val_b b1)),(Some (val_b b2))) \<Rightarrow> 
      Some (val_b (\<not>(b1 \<and> b2)))
    |_ \<Rightarrow> None
  else if opr = [nand] \<and> t \<in> {vhdl_std_ulogic, vhdl_std_logic} then
    case (v1,v2) of ((Some (val_c c1)),(Some (val_c c2))) \<Rightarrow> 
      Some (val_c (std_logic_nand c1 c2))
    |_ \<Rightarrow> None
  else if opr = [nand] \<and> t \<in> {vhdl_std_ulogic_vector, vhdl_std_logic_vector} then
    case (v1,v2) of ((Some (val_list l1)),(Some (val_list l2))) \<Rightarrow> 
      Some (val_list (std_logic_vec_nand l1 l2))
    |((Some (val_rlist l1)),(Some (val_rlist l2))) \<Rightarrow> 
      Some (val_rlist (std_logic_vec_nand l1 l2))
    |_ \<Rightarrow> None
  else if opr = [nor] \<and> t = vhdl_boolean then
    case (v1,v2) of ((Some (val_b b1)),(Some (val_b b2))) \<Rightarrow> 
      Some (val_b (\<not>(b1 \<or> b2)))
    |_ \<Rightarrow> None
  else if opr = [nor] \<and> t \<in> {vhdl_std_ulogic, vhdl_std_logic} then
    case (v1,v2) of ((Some (val_c c1)),(Some (val_c c2))) \<Rightarrow> 
      Some (val_c (std_logic_nor c1 c2))
    |_ \<Rightarrow> None
  else if opr = [nor] \<and> t \<in> {vhdl_std_ulogic_vector, vhdl_std_logic_vector} then
    case (v1,v2) of ((Some (val_list l1)),(Some (val_list l2))) \<Rightarrow> 
      Some (val_list (std_logic_vec_nor l1 l2))
    |((Some (val_rlist l1)),(Some (val_rlist l2))) \<Rightarrow> 
      Some (val_rlist (std_logic_vec_nor l1 l2))
    |_ \<Rightarrow> None
  else if opr = [xor] \<and> t = vhdl_boolean then
    case (v1,v2) of ((Some (val_b b1)),(Some (val_b b2))) \<Rightarrow> 
      Some (val_b ((b1 \<or> b2) \<and> (\<not>(b1 \<and> b2))))
    |_ \<Rightarrow> None
  else if opr = [xor] \<and> t \<in> {vhdl_std_ulogic, vhdl_std_logic} then
    case (v1,v2) of ((Some (val_c c1)),(Some (val_c c2))) \<Rightarrow> 
      Some (val_c (std_logic_xor c1 c2))
    |_ \<Rightarrow> None
  else if opr = [xor] \<and> t \<in> {vhdl_std_ulogic_vector, vhdl_std_logic_vector} then
    case (v1,v2) of ((Some (val_list l1)),(Some (val_list l2))) \<Rightarrow> 
      Some (val_list (std_logic_vec_xor l1 l2))
    |((Some (val_rlist l1)),(Some (val_rlist l2))) \<Rightarrow> 
      Some (val_rlist (std_logic_vec_xor l1 l2))
    |_ \<Rightarrow> None
  else if opr = [xnor] \<and> t = vhdl_boolean then
    case (v1,v2) of ((Some (val_b b1)),(Some (val_b b2))) \<Rightarrow> 
      Some (val_b ((b1 \<and> b2) \<or> ((\<not> b1) \<and> (\<not> b2))))
    |_ \<Rightarrow> None
  else if opr = [xnor] \<and> t \<in> {vhdl_std_ulogic, vhdl_std_logic} then
    case (v1,v2) of ((Some (val_c c1)),(Some (val_c c2))) \<Rightarrow> 
      Some (val_c (std_logic_xnor c1 c2))
    |_ \<Rightarrow> None
  else if opr = [xnor] \<and> t \<in> {vhdl_std_ulogic_vector, vhdl_std_logic_vector} then
    case (v1,v2) of ((Some (val_list l1)),(Some (val_list l2))) \<Rightarrow> 
      Some (val_list (std_logic_vec_xnor l1 l2))
    |((Some (val_rlist l1)),(Some (val_rlist l2))) \<Rightarrow> 
      Some (val_rlist (std_logic_vec_xnor l1 l2))
    |_ \<Rightarrow> None
  else None" 

definition val_rel:: "type \<Rightarrow> rop \<Rightarrow> val option \<Rightarrow> val option \<Rightarrow> val option" where
"val_rel t opr v1 v2 \<equiv> 
  if t = vhdl_boolean then
    case (v1,v2) of ((Some (val_b b1)),(Some (val_b b2))) \<Rightarrow> 
      if opr = [=]  then Some (val_b (b1 = b2))
      else if opr = [/=] then Some (val_b (b1 \<noteq> b2))
      else if opr = [<] then Some (val_b (b1 < b2))
      else if opr = [<=] then Some (val_b (b1 \<le> b2))
      else if opr = [>] then Some (val_b (b1 > b2))
      else if opr = [>=] then Some (val_b (b1 \<ge> b2))
      else None
    |_ \<Rightarrow> None
  else if t \<in> {vhdl_bit, vhdl_character} then
    case (v1,v2) of ((Some (val_c c1)),(Some (val_c c2))) \<Rightarrow> 
      if opr = [=] then Some (val_b (c1 = c2))
      else if opr = [/=] then Some (val_b (c1 \<noteq> c2))
      else if opr = [<] then Some (val_b ((nat_of_char c1) < (nat_of_char c2)))
      else if opr = [<=] then Some (val_b ((nat_of_char c1) \<le> (nat_of_char c2)))
      else if opr = [>] then Some (val_b ((nat_of_char c1) > (nat_of_char c2)))
      else if opr = [>=] then Some (val_b ((nat_of_char c1) \<ge> (nat_of_char c2)))
      else None
    |_ \<Rightarrow> None
  else if t \<in> {vhdl_integer, vhdl_time, vhdl_positive, vhdl_natural} then
    case (v1,v2) of ((Some (val_i i1)),(Some (val_i i2))) \<Rightarrow> 
      if opr = [=] then Some (val_b (i1 = i2))
      else if opr = [/=] then Some (val_b (i1 \<noteq> i2))
      else if opr = [<] then Some (val_b (i1 < i2))
      else if opr = [<=] then Some (val_b (i1 \<le> i2))
      else if opr = [>] then Some (val_b (i1 > i2))
      else if opr = [>=] then Some (val_b (i1 \<ge> i2))
      else None
    |_ \<Rightarrow> None
  else if t = vhdl_real then
    case (v1,v2) of ((Some (val_r r1)),(Some (val_r r2))) \<Rightarrow> 
      if opr = [=] then Some (val_b (r1 = r2))
      else if opr = [/=] then Some (val_b (r1 \<noteq> r2))
      else if opr = [<] then Some (val_b (r1 < r2))
      else if opr = [<=] then Some (val_b (r1 \<le> r2))
      else if opr = [>] then Some (val_b (r1 > r2))
      else if opr = [>=] then Some (val_b (r1 \<ge> r2))
      else None
    |_ \<Rightarrow> None
  else if t \<in> {vhdl_std_logic, vhdl_std_ulogic} then
    case (v1,v2) of ((Some (val_c c1)),(Some (val_c c2))) \<Rightarrow>
      if opr = [=] then Some (val_b (c1 = c2))
      else if opr = [/=] then Some (val_b (c1 \<noteq> c2))
      else None
    |_ \<Rightarrow> None
  else if t \<in> {vhdl_std_logic_vector, vhdl_std_ulogic_vector} then
    case (v1,v2) of ((Some (val_list l1)),(Some (val_list l2))) \<Rightarrow>
      if opr = [=] then Some (val_b (l1 = l2))
      else if opr = [/=] then Some (val_b (l1 \<noteq> l2))
      else None
    |((Some (val_rlist l1)),(Some (val_rlist l2))) \<Rightarrow>
      if opr = [=] then Some (val_b (l1 = l2))
      else if opr = [/=] then Some (val_b (l1 \<noteq> l2))
      else None
    |((Some (val_list l1)),(Some (val_rlist l2))) \<Rightarrow>
      if opr = [=] then Some (val_b (l1 = l2))
      else if opr = [/=] then Some (val_b (l1 \<noteq> l2))
      else None
    |((Some (val_rlist l1)),(Some (val_list l2))) \<Rightarrow>
      if opr = [=] then Some (val_b (l1 = l2))
      else if opr = [/=] then Some (val_b (l1 \<noteq> l2))
      else None
    |_ \<Rightarrow> None
  else None" 

definition val_shift:: "type \<Rightarrow> sop \<Rightarrow> val option \<Rightarrow> val option \<Rightarrow> val option" where
"val_shift t opr v1 v2 \<equiv>
  if t = vhdl_boolstr then
    case (v1,v2) of ((Some (val_list bl)),(Some (val_i i))) \<Rightarrow> 
      if opr = [sll] then Some (val_list (sll_bools (nat i) bl))
      else if opr = [srl] then Some (val_list (srl_bools (nat i) bl))
      else if opr = [sla] then Some (val_list (sla_bools (nat i) bl))
      else if opr = [sra] then Some (val_list (sra (nat i) bl))
      else if opr = [rol] then Some (val_list (rol (nat i) bl))
      else if opr = [ror] then Some (val_list (ror (nat i) bl))
      else None
    |((Some (val_rlist bl)),(Some (val_i i))) \<Rightarrow> 
      if opr = [sll] then Some (val_rlist (sll_bools (nat i) bl))
      else if opr = [srl] then Some (val_rlist (srl_bools (nat i) bl))
      else if opr = [sla] then Some (val_rlist (sla_bools (nat i) bl))
      else if opr = [sra] then Some (val_rlist (sra (nat i) bl))
      else if opr = [rol] then Some (val_rlist (rol (nat i) bl))
      else if opr = [ror] then Some (val_rlist (ror (nat i) bl))
      else None
    | _ \<Rightarrow> None
  else if t \<in> {vhdl_bitstr, vhdl_std_logic_vector, vhdl_std_ulogic_vector} then
    case (v1,v2) of ((Some (val_list s)),(Some (val_i i))) \<Rightarrow>
      if opr = [sll] then Some (val_list (sll_bits (nat i) s))
      else if opr = [srl] then Some (val_list (srl_bits (nat i) s))
      else if opr = [sla] then Some (val_list (sla_bits (nat i) s))
      else if opr = [sra] then Some (val_list (sra (nat i) s))
      else if opr = [rol] then Some (val_list (rol (nat i) s))
      else if opr = [ror] then Some (val_list (ror (nat i) s))
      else None
    |((Some (val_rlist s)),(Some (val_i i))) \<Rightarrow>
      if opr = [sll] then Some (val_rlist (sll_bits (nat i) s))
      else if opr = [srl] then Some (val_rlist (srl_bits (nat i) s))
      else if opr = [sla] then Some (val_rlist (sla_bits (nat i) s))
      else if opr = [sra] then Some (val_rlist (sra (nat i) s))
      else if opr = [rol] then Some (val_rlist (rol (nat i) s))
      else if opr = [ror] then Some (val_rlist (ror (nat i) s))
      else None
    | _ \<Rightarrow> None
  else None"

text {* A definition of the operator rem on integers based on the VHDL manual. *}

definition rem:: "int \<Rightarrow> int \<Rightarrow> int" (infix "rem" 50) where 
"i rem j \<equiv> i - (i div j) * j"

fun expoi:: "int \<Rightarrow> nat \<Rightarrow> int" where
"expoi i 0 = 0"
|"expoi i n = i * (expoi i (n-1))"

fun expor:: "real \<Rightarrow> nat \<Rightarrow> real" where
"expor i 0 = 0"
|"expor i n = i * (expor i (n-1))"

definition val_arith:: "type \<Rightarrow> aop \<Rightarrow> val option \<Rightarrow> val option \<Rightarrow> val option" where
"val_arith t opr v1 v2 \<equiv>
  if t \<in> {vhdl_integer, vhdl_time} then
    case (v1,v2) of ((Some (val_i i1)),(Some (val_i i2))) \<Rightarrow> 
      if opr = [+] then Some (val_i (i1 + i2))
      else if opr = [-] then Some (val_i (i1 - i2))
      else if opr = [*] then Some (val_i (i1 * i2))
      else if opr = [/] then 
        if i2 = 0 then None
        else Some (val_i (i1 div i2)) 
      else if opr = [mod] then Some (val_i (i1 mod i2))
      else if opr = [rem] then Some (val_i (i1 rem i2))  
      else if opr = [**] then Some (val_i (expoi i1 (nat i2))) 
      else None
    |_ \<Rightarrow> None 
  else if t = vhdl_real then
    case (v1,v2) of ((Some (val_r r1)),(Some (val_r r2))) \<Rightarrow> 
      if opr = [+] then Some (val_r (r1 + r2))
      else if opr = [-] then Some (val_r (r1 - r2))
      else if opr = [*] then Some (val_r (r1 * r2))
      else if opr = [/] then 
        if r2 = 0 then None
        else Some (val_r (r1 div r2)) 
      else None
    | ((Some (val_r r1)),(Some (val_i i2))) \<Rightarrow> 
      if opr = [**] then Some (val_r (expor r1 (nat i2)))
      else None
    |_ \<Rightarrow> None
  else if t = vhdl_positive then
    case (v1,v2) of ((Some (val_i i1)),(Some (val_i i2))) \<Rightarrow> 
      if opr = [+] then Some (val_i (i1 + i2))
      else if opr = [-] then 
        if i1 > i2 then Some (val_i (i1 - i2))
        else None
      else if opr = [*] then Some (val_i (i1 * i2))
      else if opr = [/] then Some (val_i (i1 div i2)) 
      else if opr = [mod] then Some (val_i (i1 mod i2))
      else if opr = [rem] then Some (val_i (i1 rem i2))
      else if opr = [**] then Some (val_i (expoi i1 (nat i2)))
      else None
    |_ \<Rightarrow> None
  else if t = vhdl_natural then
    case (v1,v2) of ((Some (val_i i1)),(Some (val_i i2))) \<Rightarrow> 
      if opr = [+] then Some (val_i (i1 + i2))
      else if opr = [-] then 
        if i1 \<ge> i2 then Some (val_i (i1 - i2))
        else None
      else if opr = [*] then Some (val_i (i1 * i2))
      else if opr = [/] then 
        if i2 = 0 then None
        else Some (val_i (i1 div i2)) 
      else if opr = [mod] then Some (val_i (i1 mod i2))
      else if opr = [rem] then Some (val_i (i1 rem i2))
      else if opr = [**] then Some (val_i (expoi i1 (nat i2)))
      else None
    |_ \<Rightarrow> None
  else if t \<in> {vhdl_string, vhdl_bitstr, vhdl_boolstr, 
    vhdl_std_logic_vector, vhdl_std_ulogic_vector} then
    case (v1,v2) of ((Some (val_list s1)),(Some (val_list s2))) \<Rightarrow> 
      if opr = [&] then Some (val_list (s1@s2))
      else if opr = [+] then Some (val_list (std_logic_vec_add s1 s2))
      else if opr = [-] then Some (val_list (std_logic_vec_sub s1 s2))
      else None
    |((Some (val_list s1)),(Some (val_rlist s2))) \<Rightarrow> 
      if opr = [&] then Some (val_list (s1@s2)) 
      else None
    |((Some (val_rlist s1)),(Some (val_list s2))) \<Rightarrow> 
      if opr = [&] then Some (val_rlist (s1@s2))
      else None
    |((Some (val_rlist s1)),(Some (val_rlist s2))) \<Rightarrow> 
      if opr = [&] then Some (val_rlist (s1@s2))
      else if opr = [+] then Some (val_rlist (std_logic_vec_add s1 s2))
      else if opr = [-] then Some (val_rlist (std_logic_vec_sub s1 s2))
      else None
    |_ \<Rightarrow> None
  else None"

text {* Make a set of consecutive naturals from n1 to n2. *}

function mk_nats:: "nat \<Rightarrow> nat \<Rightarrow> nat set" where
"mk_nats n1 n2 = (
  if n1 > n2 then {}
  else if n1 = n2 then {n1}
  else {n1}\<union>(mk_nats (Suc n1) n2)
)"
by pat_completeness auto
termination mk_nats
apply (relation "measure (\<lambda>(n1,n2). n2 - n1)")
by auto

text {* A wrapper for the built-in sublist funciton. *}

definition get_sl:: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list" where
"get_sl l n1 n2 \<equiv> sublist l (mk_nats n1 n2)"

text {* Find the type of the expression. *}

primrec exp_type:: "expression \<Rightarrow> type option" where
"exp_type (uexp opr e) = exp_type e"
|"exp_type (bexpl e1 opr e2) = (
  let t1 = exp_type e1;
      t2 = exp_type e2 in
  if t1 = t2 \<and> t1 \<noteq> None then t1 else None)"
|"exp_type (bexpr e1 opr e2) = (
  let t1 = exp_type e1;
      t2 = exp_type e2 in
  if t1 = t2 \<and> t1 \<noteq> None then Some vhdl_boolean else None)"
|"exp_type (bexps e1 opr e2) = (
  let t1 = exp_type e1 in
  if t1 \<noteq> None then t1 else None)"
|"exp_type (bexpa e1 opr e2) = (
  let t1 = exp_type e1;
      t2 = exp_type e2 in
  if t1 = t2 \<and> t1 \<noteq> None then t1 else None)"
|"exp_type (exp_sig s) = Some (fst (snd s))"
|"exp_type (exp_prt p) = Some (fst (snd p))"
|"exp_type (exp_var v) = Some (fst (snd v))"
|"exp_type (exp_con c) = Some (fst c)"
|"exp_type (exp_nth e e2) = (
  case exp_type e of 
   Some t \<Rightarrow> (
   if t = vhdl_string then Some vhdl_character
   else if t = vhdl_bitstr then Some vhdl_bit
   else if t = vhdl_boolstr then Some vhdl_boolean
   else if t = vhdl_std_logic_vector then Some vhdl_std_logic
   else if t = vhdl_std_ulogic_vector then Some vhdl_std_ulogic
   else None
  )
  |_ \<Rightarrow> None
)"
|"exp_type (exp_sl e1 e2 e3) = exp_type e1"
|"exp_type (exp_tl e) = (
  case exp_type e of Some t \<Rightarrow> (
    if t = vhdl_character then Some vhdl_string
    else if t = vhdl_bit then Some vhdl_bitstr
    else if t = vhdl_boolean then Some vhdl_boolstr
    else if t = vhdl_std_logic then Some vhdl_std_logic_vector
    else if t = vhdl_std_ulogic then Some vhdl_std_ulogic_vector
    else None
  )
  |_ \<Rightarrow> None
)"
|"exp_type (exp_trl e) = (
  case exp_type e of Some t \<Rightarrow> (
    if t = vhdl_character then Some vhdl_string
    else if t = vhdl_bit then Some vhdl_bitstr
    else if t = vhdl_boolean then Some vhdl_boolstr
    else if t = vhdl_std_logic then Some vhdl_std_logic_vector
    else if t = vhdl_std_ulogic then Some vhdl_std_ulogic_vector
    else None
  )
  |_ \<Rightarrow> None
)"

text {* init_val_exp computes the inital value of the expression. 
That is, the values of signals/ports/variables are the initial values
or the default expression initial values. *}

fun init_val_exp:: "type \<Rightarrow> expression \<Rightarrow> val option" where
"init_val_exp t (uexp opr e) = 
  val_uop t opr (init_val_exp t e)"
|"init_val_exp t (bexpl e1 lopr e2) = 
  val_logical t lopr (init_val_exp t e1) (init_val_exp t e2)"
|"init_val_exp t (bexpr e1 ropr e2) = (
  case (exp_type e1, exp_type e2) of
   (Some t1, Some t2) \<Rightarrow>
   if t1 = t2 then
     val_rel t ropr (init_val_exp t1 e1) (init_val_exp t1 e2)
   else None
  |_ \<Rightarrow> None
)"
|"init_val_exp t (bexps e1 sopr e2) = 
  val_shift t sopr (init_val_exp t e1) (init_val_exp t e2)"
|"init_val_exp t (bexpa e1 aopr e2) = (
  case (exp_type e1, exp_type e2) of
   (Some t1, Some t2) \<Rightarrow> 
    val_arith t aopr (init_val_exp t1 e1) (init_val_exp t2 e2)
  |_ \<Rightarrow> None
)"
|"init_val_exp t (exp_sig s) = init_val_exp t (snd (snd (snd s)))"
|"init_val_exp t (exp_prt p) = init_val_exp t (snd (snd (snd (snd p))))"
|"init_val_exp t (exp_var v) = init_val_exp t (snd (snd v))"
|"init_val_exp t (exp_con c) = Some (snd c)"
|"init_val_exp t (exp_nth e1 e2) = (
  case exp_type e1 of 
   Some t1 \<Rightarrow> (
    case (init_val_exp t1 e1, init_val_exp vhdl_natural e2) of
     (Some (val_list l), Some (val_i n)) \<Rightarrow> Some (nth l (nat n))
    |(Some (val_rlist l), Some (val_i n)) \<Rightarrow> Some (nth (rev l) (nat n))
    |_ \<Rightarrow> None)
   |_ \<Rightarrow> None
)"
|"init_val_exp t (exp_sl e1 e2 e3) = (
  case exp_type e1 of 
   Some t1 \<Rightarrow> (
    case (init_val_exp t1 e1, init_val_exp vhdl_natural e2, init_val_exp vhdl_natural e3) of
     (Some (val_list l), Some (val_i n1), Some (val_i n2)) \<Rightarrow> (
      if n1 \<le> n2 then Some (val_list (get_sl l (nat n1) (nat n2)))
      else Some (val_list (get_sl l (nat n2) (nat n1))))
    |(Some (val_rlist l), Some (val_i n1), Some (val_i n2)) \<Rightarrow> (
      if n1 \<le> n2 then Some (val_rlist (rev (get_sl (rev l) (nat n1) (nat n2))))
      else Some (val_rlist (rev (get_sl (rev l) (nat n2) (nat n1)))))
    |_ \<Rightarrow> None)
   |_ \<Rightarrow> None
)"
|"init_val_exp t (exp_tl e) = (
  case exp_type e of 
   Some t1 \<Rightarrow> (
    case init_val_exp t1 e of 
     Some v \<Rightarrow> Some (val_list [v])
    |_ \<Rightarrow> None)
  |_ \<Rightarrow> None
)"
|"init_val_exp t (exp_trl e) = (
  case exp_type e of
   Some t1 \<Rightarrow> (
    case init_val_exp t1 e of 
     Some v \<Rightarrow> Some (val_rlist [v])
    |_ \<Rightarrow> None)
  |_ \<Rightarrow> None
)"

definition init_val_exp_t:: "expression \<Rightarrow> val option" where
"init_val_exp_t e \<equiv> 
  let this_type = exp_type e in
  case this_type of Some t \<Rightarrow> init_val_exp t e
  |None \<Rightarrow> None"

text {* Get the initial value of a VHDL variable. This variable must be of type natural. *}

definition get_init_val:: "variable \<Rightarrow> nat" where
"get_init_val v \<equiv> 
  case init_val_exp_t (exp_var v) of Some (val_i i) \<Rightarrow> nat i 
  |None \<Rightarrow> 0
"    

text {* state_val_exp computes the value of the expression in the current state.  *}

primrec state_val_exp:: "type \<Rightarrow> expression \<Rightarrow> vhdl_state \<Rightarrow> val option" where
"state_val_exp t (uexp opr e) state = 
  val_uop t opr (state_val_exp t e state)"
|"state_val_exp t (bexpl e1 lopr e2) state = 
  val_logical t lopr (state_val_exp t e1 state) (state_val_exp t e2 state)"
|"state_val_exp t (bexpr e1 ropr e2) state = (
  case ((exp_type e1),(exp_type e2)) of 
   (Some t1, Some t2) \<Rightarrow> (
    if t1 = t2 then
      val_rel t1 ropr (state_val_exp t1 e1 state) (state_val_exp t1 e2 state)
    else None)
  |_ \<Rightarrow> None)"
|"state_val_exp t (bexps e1 sopr e2) state = 
  val_shift t sopr (state_val_exp t e1 state) (state_val_exp vhdl_natural e2 state)"
|"state_val_exp t (bexpa e1 aopr e2) state = (
  case ((exp_type e1),(exp_type e2)) of 
   (Some t1, Some t2) \<Rightarrow> (* The expression has the same type as e1. e2 may have a different type. *)
    val_arith t1 aopr (state_val_exp t1 e1 state) (state_val_exp t2 e2 state)
  |_ \<Rightarrow> None)"
|"state_val_exp t (exp_sig s) state = state_sp state (sp_s s)"
|"state_val_exp t (exp_prt p) state = state_sp state (sp_p p)"
|"state_val_exp t (exp_var v) state = state_var state v"
|"state_val_exp t (exp_con c) state = Some (snd c)"
|"state_val_exp t (exp_nth e e2) state = (
  case exp_type e of 
   Some t1 \<Rightarrow> (
    case (state_val_exp t1 e state, state_val_exp vhdl_natural e2 state) of 
     (Some (val_list l), Some (val_i n)) \<Rightarrow> Some (nth l (nat n))
    |(Some (val_rlist l), Some (val_i n)) \<Rightarrow> Some (nth (rev l) (nat n))
    |_ \<Rightarrow> None)
   |_ \<Rightarrow> None
)"
|"state_val_exp t (exp_sl e1 e2 e3) state = (
  case exp_type e1 of 
   Some t1 \<Rightarrow> (
    case (state_val_exp t1 e1 state, state_val_exp vhdl_natural e2 state, state_val_exp vhdl_natural e3 state) of
     (Some (val_list l), Some (val_i n1), Some (val_i n2)) \<Rightarrow> (
      if n1 \<le> n2 then Some (val_list (get_sl l (nat n1) (nat n2)))
      else Some (val_list (get_sl l (nat n2) (nat n1))))
    |(Some (val_rlist l), Some (val_i n1), Some (val_i n2)) \<Rightarrow> (
      if n1 \<le> n2 then Some (val_rlist (rev (get_sl (rev l) (nat n1) (nat n2))))
      else Some (val_rlist (rev (get_sl (rev l) (nat n2) (nat n1)))))
    |_ \<Rightarrow> None)
   |_ \<Rightarrow> None
)"
|"state_val_exp t (exp_tl e) state = (
  case exp_type e of 
   Some t1 \<Rightarrow> (
    case state_val_exp t1 e state of
     Some v \<Rightarrow> Some (val_list [v])
    |_ \<Rightarrow> None)
  |_ \<Rightarrow> None
)"
|"state_val_exp t (exp_trl e) state = (
  case exp_type e of 
   Some t1 \<Rightarrow> (
    case state_val_exp t1 e state of
     Some v \<Rightarrow> Some (val_rlist [v])
    |_ \<Rightarrow> None)
   |_ \<Rightarrow> None
)"

definition state_val_exp_t:: "expression \<Rightarrow> vhdl_state \<Rightarrow> val option" where
"state_val_exp_t e state \<equiv> 
  let this_type = exp_type e in
  case this_type of Some t \<Rightarrow> state_val_exp t e state
  |None \<Rightarrow> None"

text {* Convert a val optoin to a natural. *}

definition nat_of_val_op:: "val option \<Rightarrow> nat" where
"nat_of_val_op vop \<equiv> 
  case vop of None \<Rightarrow> 0
  |Some v \<Rightarrow> (
    case v of val_i i \<Rightarrow> nat i
    |val_r r \<Rightarrow> nat (floor r)
    |val_b True \<Rightarrow> 1
    |val_b False \<Rightarrow> 0
    |_ \<Rightarrow> 0
  )
"

primrec state_val_expl_t:: "expression list \<Rightarrow> vhdl_state \<Rightarrow> (val option) list" where
"state_val_expl_t [] state = []"
|"state_val_expl_t (x#xs) state = (state_val_exp_t x state)#(state_val_expl_t xs state)"

primrec list_val:: "(val option) list \<Rightarrow> val list \<Rightarrow> val option" where
"list_val [] acc = Some (val_list acc)"
|"list_val (x#xs) acc = (
  case x of Some v \<Rightarrow> list_val xs (acc@[v])
  |None \<Rightarrow> None
)"

definition sigprt_init_val:: "sigprt \<Rightarrow> val option" where
"sigprt_init_val sp \<equiv>
  case sp of 
   sp_s s \<Rightarrow> init_val_exp_t  (snd (snd (snd s)))
  |sp_p p \<Rightarrow> init_val_exp_t (snd (snd (snd (snd p))))"

definition var_init_val:: "variable \<Rightarrow> val option" where
"var_init_val v \<equiv> init_val_exp_t (snd (snd v))"

end