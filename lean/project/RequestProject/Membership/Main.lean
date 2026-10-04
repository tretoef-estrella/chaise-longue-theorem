module

public import RequestProject.Membership.Vand
public import RequestProject.Membership.Box
public import RequestProject.Membership.Defs
public import RequestProject.Membership.Theorem

/-!
# `q_membership.md`: the membership lemma of the odd box

Entry point of the formalization of `q_membership.md` (namespace `Membership`). The folders
`RequestProject/Pfaffian/` and `RequestProject/RankTwo/`, `ColOne.Dab`, `Tight.vand`,
`Odd3.IsPairs` and `Odd3.supp` are used unchanged. Any commutative ring; nothing is divided.

* Part V, Theorem V (`Vand`): (V1) `V1`; (V2) `V2`; (V3) the definition `PolyIn`, the columns
  `polyIn_pow`, `polyIn_Ev`, `polyIn_Od`, and the divisibility `V3`.
* Part H, Theorem H (`Box`): (H1) `H1`; (H2) `H2`; (H3) `H3`.
* Part M, Definitions (`Defs`): `pairDy`, `DPy`, `UB`, `U`.
* Part M, Theorem M (`Theorem`): (M1) `M1`; (M2) `M2a`, `M2b`; (M3) `M3_pos` (the case `ℓ ≥ 1`,
  with `ℓ = l + 1`), `M3_zero` (the case `ℓ = 0`); (M4) `M4a`, `M4b`.
-/
