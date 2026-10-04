#!/bin/zsh
# STEP 6 — md5 of the published pieces vs the md5 prefixes recorded in AUDIT_LOG.md (lines 328, 337, 347).
# Expected: MATCH for q_col_count (dc5cd5d4), q_col_upper (99de146a), q_col_assembly (d8542bbf). Time: < 1 s.
cd "${0:A:h}/.."
echo "# md5 of published pieces (material/lean/pieces), $(date '+%F %T')"; md5 -r material/lean/pieces/*.md; echo
echo "# md5 prefixes recorded in AUDIT_LOG.md (lines 328, 337, 347): q_col_count dc5cd5d4, q_col_upper 99de146a, q_col_assembly d8542bbf"
for f in q_col_count:dc5cd5d4 q_col_upper:99de146a q_col_assembly:d8542bbf; do n=${f%%:*}; h=${f##*:}; a=$(md5 -q material/lean/pieces/$n.md)
  case $a in $h*) echo "$n: MATCH ($a)";; *) echo "$n: MISMATCH ($a vs $h)";; esac; done
