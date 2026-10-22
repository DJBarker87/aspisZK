#!/usr/bin/env python3
import hashlib
import json
import re
from pathlib import Path

P = Path(__file__).resolve().parent
ROOT = next(p for p in P.parents if
            (p / "lean-candidates/s4-tx2-full-source-owned-cut-v1-20261021/source-pins/Funs.lean").is_file())

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def tokens(text):
    return re.findall(r"[A-Za-z0-9_]+|[^\sA-Za-z0-9_]", text)

def need(condition, message):
    if not condition:
        raise SystemExit("FAIL: " + message)

m = json.loads((P / "manifest.json").read_text())
src = P / "sources/S4ReaderEActualWideCanonicalV1.lean"
gen = ROOT / m["generated_funs"]["path"]
need(sha(src) == m["source_sha256"], "source hash")
need(sha(gen) == m["generated_funs"]["sha256"], "generated Funs hash")
f = gen.read_text()
start = f.index("def verifier.Reader.e\n")
end = f.index("\n/-- [aspis_r1_cost_probe::verifier::CHECKPOINT_FIXED]", start)
block = f[start:end]
a = src.read_text()
start2 = a.index("def readerE (")
end2 = a.index("\n\ntheorem readerE_success_canonical", start2)
cut = a[start2:end2]
generated = block.split(":= do\n", 1)[1]
adapted = cut.split(":= do\n", 1)[1]
for old, new in [
    ("verifier.Reader.raw", "raw"),
    ("aspis_core.field.wide_exact.WideExact.from_le_bytes", "actualCurrentWideDecoder"),
    ("core.option.Option.ok_or", "optionOkOr"),
]:
    generated = generated.replace(old, new)
need(tokens(generated) == tokens(adapted), "Reader.e operation-body tokens")
need("(raw : (n : Usize) → Reader → Result (Array Std.U8 n × Reader))" in a,
     "dependent raw ABI")
need("sorry" not in a, "sorry in Lean source")
r = json.loads((P / "attempt/receipt.json").read_text())
need(r["exit_status"] == 0, "compile exit")
need(r["source_sha256_start"] == m["source_sha256"] == r["source_sha256_end"],
     "launch/end source pin")
need(r["object_sha256"] == m["object_sha256"], "object receipt pin")
log = (P / "attempt/lean.log").read_text()
need("sorryAx" not in log, "sorryAx in axiom audit")
for theorem in m["axiom_audits"]:
    need(theorem in log, "missing axiom audit " + theorem)
need(sha(P / "dependencies/coherent-closure-manifest.json") ==
     m["coherent_import_overlay"]["sha256"], "closure manifest hash")
for owner in m["direct_imports"]:
    if owner.get("source", "").startswith("dependencies/"):
        need(sha(P / owner["source"]) == owner["source_sha256"],
             "imported source hash: " + owner["module"])
closure = json.loads((P / "dependencies/coherent-closure-manifest.json").read_text())
by_module = {x["module"]: x for x in closure["modules"]}
for module in ["ExtractedRecordByteCanonicality", "AspisR1RecordParser.Types"]:
    expected = next(x["object_sha256"] for x in m["direct_imports"]
                    if x["module"] == module or
                    x["module"] == module + " selected transitive owner")
    need(by_module[module]["sha256"] == expected,
         "selected closure object hash: " + module)
print("PASS source, operation body, dependent raw ABI, receipts, imports and axiom audit")
