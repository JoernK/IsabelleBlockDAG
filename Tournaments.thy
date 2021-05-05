(*  Title:      HOL/Tournaments
    Author:     Joern Kussmaul
*)

section \<open>Tournament\<close>

theory Tournaments
  imports Main
begin

locale dag_tournament = partial_order + 
  assumes ex_inf: "\<exists> inf. is_inf x y inf"
begin


end