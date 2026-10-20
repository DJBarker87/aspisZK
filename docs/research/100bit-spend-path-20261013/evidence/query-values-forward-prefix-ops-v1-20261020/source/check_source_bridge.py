#!/usr/bin/env python3
"""Check the frozen query_values prefix and its typed Aeneas body adapter."""
from pathlib import Path
import hashlib
import re

root = Path(__file__).parent.parent
original = (root / "source/original-body-cut.rs").read_bytes()
helper = (root / "source/candidate-helper.rs").read_text()
generated = (root / "generated/raw/Funs.lean").read_text()
adapter = (root / "lean/ForwardOps.lean").read_text()
raw_types = (root / "generated/raw/Types.lean").read_text()
compiled_types = (root / "lean/Types.lean").read_text()

expected_source = (
    b"\n    let i = a.next;\n"
    b"    let u = p.queries[i] as usize;\n"
    b"    let q = opening(proof, i);\n"
    b"    let dots = crate::fast_dots::four_dots(q, g);"
)
assert original == expected_source
assert hashlib.sha256(original).hexdigest() == "d46397152fdf62c2da775e3a45d5423ed5bdb40db421b5496fe391e0cadf5024"
candidate_prefix = (
    "    let i = a.next;\n"
    "    let u = p.queries[i] as usize;\n"
    "    let q = opening(proof, i);\n"
    "    let dots = crate::fast_dots::four_dots(q, g);"
)
helper_start = helper.index("    let i = a.next;")
helper_end = helper.index("    let dots = crate::fast_dots::four_dots(q, g);", helper_start) + len(
    "    let dots = crate::fast_dots::four_dots(q, g);"
)
assert helper[helper_start:helper_end] == candidate_prefix

def body(text: str, declaration: str) -> str:
    match = re.search(declaration + r"\b.*?:= do\n(?P<body>.*?)\n\n(?:private theorem|theorem|end AspisR1Stage2QueryTailCut)", text, re.S)
    assert match, declaration
    return match.group("body")

raw_body = body(generated, r"def verifier\.candidate\.query_values_forward_prefix")
adapter_body = body(adapter, r"def query_values_forward_prefix_ops")
raw_body = raw_body.replace("verifier.candidate.opening", "openingOp")
raw_body = raw_body.replace("fast_dots.four_dots", "fourDotsOp")
norm = lambda value: re.sub(r"\s+", " ", value).strip()
assert norm(raw_body) == norm(adapter_body)
assert "fourDotsOp q g" in adapter_body
assert compiled_types == raw_types.replace("set_option maxHeartbeats 1000000\n", "").replace("set_option maxRecDepth 2048\n", "")
print("PASS: frozen Rust prefix bytes, candidate helper statements, and full emitted Lean body agree.")
print("PASS: typed adapter changes exactly the `opening` and `four_dots` external call names to explicit parameters.")
print("PASS: compiled Types owner differs from raw generated Types only by removing the two resource overrides.")
