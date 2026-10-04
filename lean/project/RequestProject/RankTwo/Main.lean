module

public import RequestProject.RankTwo.Shift
public import RequestProject.RankTwo.Homog
public import RequestProject.RankTwo.Update
public import RequestProject.RankTwo.TopCoeff
public import RequestProject.RankTwo.OddDefs
public import RequestProject.RankTwo.Key
public import RequestProject.RankTwo.OddBox

/-!
# `q_rank_two.md`: the rank-two update of a bordered Pfaffian, and the odd box

Entry point of the formalization of `q_rank_two.md` (namespace `RankTwo`). The folder
`RequestProject/Pfaffian/` (`q_pfaffian.md`) and `ColOne.Dab` are used unchanged.

* Part R, Theorem R (over an arbitrary commutative ring):
  (R1) `R1` (`Shift`); (R2) `R2` (`Shift`); (R3) `R3_pf`, `R3_bpf` (`Homog`);
  (R4) `R4`, `R4'` (`Update`); (R5) `R5_pf`, `R5_bpf` (`TopCoeff`).
* Part S (`h ≥ 1`, `r = 2h + 1`): the definitions `omega`, `Wm`, `Lm`, `Hm`, `Ev`, `Od`
  (`OddDefs`); (S0) `omega_swap`, `omega_self`, `Wm_isAlt`, `Lm_isAlt`, `Hm_isAlt`;
  (S1) `S1`, `S1_Wm`, `S1_top`; (S3) `S3` (`OddDefs`); (S2) `S2_scalar`, `S2` (`Key`);
  (S4) `S4_i`, `S4_ii`; (S5) `S5a`, `S5a_of_le`, `S5a_of_ge`, `S5b`, `S5b_of_le`,
  `S5b_of_gt` (`OddBox`).
-/
