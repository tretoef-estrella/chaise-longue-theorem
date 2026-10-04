module

public import RequestProject.OddLayers.Roots

/-!
# `q_oddbox_layers.md`: the odd box, layers and roots

Entry point collecting the formalization of `q_oddbox_layers.md` (namespace `OddLayers`):
* Part L, Definition (layers): `layerS` in `RequestProject/OddLayers/Defs.lean`;
* Theorem L, (E) and (L2): `exchange`, `FS_le_FS_subE` in `RequestProject/OddLayers/Exchange.lean`
  (with the row bookkeeping of the proof of (E) in `RequestProject/OddLayers/Rows.lean`);
* Theorem L, (L1), (L3), (L4), (L5): `FS_antitone`, `isInterlaced_layerS`,
  `layerS_succ_subset`, `layerS_eq_empty`, `Zgt_ZS_eq_ZS_layerS`, `card_ZS_eq_sum` in
  `RequestProject/OddLayers/Layers.lean`;
* Theorem R, (R1)–(R4): `shape_eq_root_iff`, `ZS_root_even_eq_closedPointed`,
  `card_ZS_root_even`, `FS_root_even`, `layerS_root_even_zero`, `layerS_root_even_pos`,
  `card_ZS_root_odd` in `RequestProject/OddLayers/Roots.lean`.
-/
