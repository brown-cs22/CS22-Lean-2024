import Mathlib.Data.Set.Basic

macro "extensionality" : tactic =>
  `(tactic| first | apply Set.ext | apply funext | apply propext)

macro "set_simplify" : tactic =>
  `(tactic | simp only [Set.mem_union, Set.mem_compl_iff,
                        Set.mem_inter_iff, Set.mem_diff] at *)
