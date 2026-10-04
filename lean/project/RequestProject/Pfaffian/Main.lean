module

public import RequestProject.Pfaffian.Basic
public import RequestProject.Pfaffian.Perm
public import RequestProject.Pfaffian.Expand
public import RequestProject.Pfaffian.Matching
public import RequestProject.Pfaffian.Bordered
public import RequestProject.Pfaffian.ExpandVar
public import RequestProject.Pfaffian.Laplace
public import RequestProject.Pfaffian.OddBox

/-!
# `q_pfaffian.md`: Pfaffians and bordered Pfaffians

Entry point of the formalization of `q_pfaffian.md` (namespace `Pfaffian`):

* Part A (`Basic`, `Perm`, `Expand`, `Matching`): `IsAlt`, `pf`, (A0) `pf_odd`, `pf_two`,
  `pf_four`; (A2) `pf_perm`; (A4) `eps`, `pf_expand` (and the variants `pf_expand_gen`,
  `pf_expand_fam`); (A3) `pf_eq_zero_of_rows`; (A5) `pf_add_row`; (A1) `IsMatching`,
  `crossings`, `pf_eq_sum_matchings`.
* Part B (`Bordered`, `ExpandVar`, `Laplace`): `bmat`, `bpf`; (B0) `bpf_odd`,
  `bpf_eq_zero_of_lt`; (B1) `bpf_perm_vars`, `bpf_perm_borders`; (B2) `bpf_add_border`,
  `bpf_eq_zero_of_border_eq`, `bpf_expand_last`; (B3) `bpf_square`; (B4) `bpf_expand_var`,
  `bpf_expand_var_zero`; (B5) `bpf_laplace`.
* Part C (`OddBox`): `ay`, `ay_isAlt`, `Pf`, `Pfe`; (C1) `C1`, (C2) `C2`, (C3) `C3`,
  (C4) `C4_eq_zero`, `C4`, (C5) `C5`, (C6) `C6`, `C6_e`.
-/
