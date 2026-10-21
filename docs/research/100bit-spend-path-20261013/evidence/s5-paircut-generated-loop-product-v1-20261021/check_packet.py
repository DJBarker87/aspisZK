#!/usr/bin/env python3
from pathlib import Path
import hashlib
import json
import re
import subprocess

P = Path(__file__).resolve().parent


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def section(text: str, start: str, end: str) -> str:
    i = text.index(start)
    return text[i:text.index(end, i + len(start))]


manifest = json.loads((P / "manifest.json").read_text())

# Each selected proof/runtime producer is tied to the exact compiled source and
# object recorded by its immutable run receipt.
for mod in manifest["modules"]:
    source = P / mod["source"]
    receipt = json.loads((P / mod["receipt"]).read_text())
    assert sha(source) == mod["source_sha256"] == receipt["source_sha256"], mod["module"]
    assert receipt["object_sha256"] == mod["object_sha256"], mod["module"]
    assert receipt["exit_status"] == 0, mod["module"]

# The exact generated loop implementation used by the proof agrees with the
# retained v23 Aeneas output at both the body and whole-loop declarations.
v23 = (P / "extractor/extraction/generated/AspisR1WeightsPairCut/Funs.lean").read_text()
original = (P / "generated-runtime/original/Funs.lean").read_text()
body_start = "def weights.push_byte_products_loop.body"
body_end = "def weights.push_byte_products_loop\n"
loop_start = "def weights.push_byte_products_loop\n"
loop_end = "def weights.push_byte_products\n"
assert section(v23, body_start, body_end) == section(original, body_start, body_end)
assert section(v23, loop_start, loop_end) == section(original, loop_start, loop_end)

# The transparent-reader parent is a separate normalized extraction. Its
# retained reader checker establishes that the selected body is the emitted
# checked-slice sequence modulo decoder substitution. The PairCut loop bodies
# consumed above are exactly the same bytes in both extraction outputs.
reader_root = P / "reader-extraction/extraction"
reader_generated = (reader_root / "AspisR1WeightsPairCut.Funs.lean").read_text()
assert sha(reader_root / "AspisR1WeightsPairCut.Funs.lean") == \
    "55afbf00a81ff85231d835ad681e38f71bcd28203f0e3f22d5c22cb0b568bf18"
subprocess.run(["python3", str(reader_root / "check_reader_source.py")], check=True)
assert section(reader_generated, body_start, body_end) == section(original, body_start, body_end)
assert section(reader_generated, loop_start, loop_end) == section(original, loop_start, loop_end)

# Funs.lean changes only the decoder callee, leaving the generated source body
# and all other emitted definitions byte-identical.
patched = (P / "generated-runtime/AspisR1WeightsPairCut/Funs.lean").read_text()
old = (
    "def field.WideExact.from_le_bytes\n"
    "  (_bytes : Slice Std.U8) : Result (Option field.WideExact) := do\n"
    "  fail panic"
)
new = (
    "def field.WideExact.from_le_bytes\n"
    "  (bytes : Slice Std.U8) : Result (Option field.WideExact) :=\n"
    "  AspisR1S5PairCutTransparentReaderV1.actualPairDecoder bytes"
)
assert original.count(old) == 1
assert patched == original.replace(old, new, 1)

# FunsExternal changes are restricted to adding imports/instance and removing
# precisely the three fail-panic EbyK declarations.
template = (P / "generated-runtime/original/FunsExternal_Template.lean").read_text()
external = (P / "generated-runtime/AspisR1WeightsPairCut/FunsExternal.lean").read_text()
expected = template
for name in ("new", "push", "finish"):
    marker = f"axiom fast_pairing.EbyKDot.{name}"
    assert expected.count(marker) == 1, marker
    pos = expected.index(marker)
    start = expected.rfind("/--", 0, pos)
    next_doc = expected.find("/--", pos)
    end = len(expected) if next_doc < 0 else next_doc
    expected = expected[:start] + expected[end:]
needle = "import AspisR1WeightsPairCut.Types\n"
assert expected.count(needle) == 1
expected = expected.replace(
    needle,
    needle + "import S5PairCutTransparentReaderAdapterV1\nimport EbyKConcreteOpsInstanceV1\n",
    1,
)
needle = "open AspisR1WeightsPairCut\n"
instance = (
    "open AspisR1WeightsPairCut\n\n"
    "instance installedSourceOps : AspisR1WeightsPairCut.fast_pairing.EbyKDotOps :=\n"
    "  AspisR1S5EbyKConcreteOpsInstanceV1.sourceOps\n\n"
)
assert expected.count(needle) == 1
expected = expected.replace(needle, instance, 1)
assert external == expected

# The candidate Rust input and the frozen baseline bytes are identical, as
# declared by the retained extraction manifest.
ext = json.loads((P / "extractor/manifest.json").read_text())
source = P / "extractor/candidate/input/source.rs"
frozen = P / "extractor/candidate/input/frozen-weights-b2727acd3.rs"
assert sha(source) == sha(frozen) == ext["basis_source_sha256"]
assert ext["source_byte_equality"].startswith("the retained candidate source snapshot equals")

# The parent Pair extraction remains normalized. This is a checked disclosure,
# not a source-equivalence claim: the balanced spans differ and the retained
# audit records the precise helper extraction/array-equality normalization.
span_audit = json.loads((P / "extractor/span-audit.json").read_text())
assert span_audit["equivalence_status"].startswith("not proved")
assert span_audit["frozen_pair"]["sha256"] != span_audit["candidate_pair"]["sha256"]
assert span_audit["normalization_delta"]
assert sha(P / "extractor/candidate/input/normalized-harness-lib.rs") == \
    span_audit["retained_full_files"]["candidate_translation_input"]["sha256"]

# No compiled artifacts are part of a source-only evidence packet.
for item in manifest["files"]:
    path = P / item["path"]
    assert path.is_file(), item["path"]
    assert sha(path) == item["sha256"], item["path"]
    assert path.suffix not in {".olean", ".ilean", ".llbc", ".o", ".a"}, item["path"]

print("PASS: source/object receipt pins, reader/body/loop identities, exact runtime adapter patch, normalized-parent disclosure, frozen input, and source-only file inventory")
