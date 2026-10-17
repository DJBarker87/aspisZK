#!/usr/bin/env python3
"""Compare the two loop executable blocks in the 04fc candidate and old pin."""
import hashlib, re, sys
candidate = sys.argv[1] if len(sys.argv) > 1 else "/tmp/terminal-indexed-loops-candidate-20261016-v3-local/Funs.lean"
prior = sys.argv[2] if len(sys.argv) > 2 else "/tmp/fromfn-copy-indexed-20261016/output/generated/AspisR1SelectedMaskProbe/Funs.lean"
for name in ("composition_parts_loop0", "composition_parts_loop1"):
    blocks = []
    for path in (candidate, prior):
        source = open(path, encoding="utf-8").read()
        marker = "def pool_v1.pair_forest_semantic_terminal." + name
        at = source.index(marker)
        start = source.rfind("/--", 0, at)
        end = source.index("partial_fixpoint", at) + len("partial_fixpoint")
        block = re.sub(r"/--.*?-/\n", "", source[start:end], flags=re.S)
        blocks.append(block)
    left, right = (hashlib.sha256(block.encode()).hexdigest() for block in blocks)
    print(f"{name}: candidate={left} prior={right} equal={blocks[0] == blocks[1]}")
    if blocks[0] != blocks[1]:
        raise SystemExit(1)
