#!/usr/bin/env python3
"""Build PAPER_OFICIAL_v12.md from v11 by anchored edits.

Every edit is (label, old, new). The old text must occur EXACTLY once in the
current text, or the build stops. The edits are applied in order. The parts
p1_front.py ... p5_back.py each define a list EDITS.

Grepy Mandalay, 4 October 2026.
"""
import hashlib, importlib, sys, pathlib

HERE = pathlib.Path(__file__).parent
SRC = HERE / "v11_source.md"
OUT = HERE / "PAPER_OFICIAL_v12.md"
PARTS = ["p1_front", "p2_sec6", "p3_sec8", "p4_sec9", "p5_back", "p6_gate", "p7_lupa"]

def main():
    text = SRC.read_text(encoding="utf-8")
    assert hashlib.md5(SRC.read_bytes()).hexdigest() == "7b3db0d60481a949dd655626fc31bfa7", "v11 source changed"
    n = 0
    sys.path.insert(0, str(HERE))
    for part in PARTS:
        try:
            mod = importlib.import_module(part)
        except ModuleNotFoundError:
            print(f"(part {part} not written yet)")
            continue
        for label, old, new in mod.EDITS:
            c = text.count(old)
            if c != 1:
                print(f"FAIL {part}:{label}: old text occurs {c} times")
                print("----- old -----")
                print(old[:400])
                sys.exit(1)
            text = text.replace(old, new)
            n += 1
            print(f"ok {part}:{label}")
    OUT.write_text(text, encoding="utf-8")
    print(f"{n} edits; wrote {OUT} ({len(text.splitlines())} lines), md5 {hashlib.md5(text.encode('utf-8')).hexdigest()}")

if __name__ == "__main__":
    main()
