#!/usr/bin/env python3
"""Check exact installed operation maps and their common Rust source pin."""
from pathlib import Path
import hashlib, json

P = Path(__file__).resolve().parent
REPO = P.parents[4]
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def repo_path(p):
    path = REPO / p
    assert path.is_file(), p
    return path

for line in (P / "SHA256SUMS").read_text().splitlines():
    digest, name = line.split("  ", 1)
    assert sha(P / name) == digest, name
r = json.loads((P / "receipts/receipt.json").read_text())
m = json.loads((P / "source-operation-map.json").read_text())
assert r["schema"] == "focused-lean-receipt-v1" and r["exit_status"] == 0
assert r["peak_rss_bytes"] == 3698573312 and r["swap_bytes"] == 0
assert r["axioms"] == ["propext", "Classical.choice", "Quot.sound"]
assert sha(P / "sources/S4V10InstalledOperationSlotsV1.lean") == r["source_sha256"]
assert sha(Path(r["object_path_at_check"])) == r["object_sha256"]
assert sha(Path(r["compiler"])) == r["compiler_sha256"]
assert not list(P.rglob("*.olean")), "source-only packet must not include Lean binaries"
for name, pin in r["direct_imports"].items():
    assert sha(repo_path(pin["source_path"])) == pin["source_sha256"], name + " source"
    assert sha(Path(pin["object_path"])) == pin["object_sha256"], name + " object"

# Same exact Rust file was used for the V10 crate, EbyKFinish extraction and
# transparent CurrentWide extraction. Check each independent producer pin.
shared = m["shared_rust_source"]
assert sha(repo_path(shared["path"])) == shared["sha256"] == "6260fa9d179328714e7df59640abb7a76a326e98900993ce7d3da98c6411d10b"
v10 = json.loads(repo_path(m["owners"]["v10"]["source_inventory"]).read_text())
assert next(f["sha256"] for f in v10["files"] if f["path"] == shared["path"]) == shared["sha256"]
eby = json.loads(repo_path(m["owners"]["eby_k_finish"]["source_pins"]).read_text())
cur = json.loads(repo_path(m["owners"]["current_wide"]["source_pins"]).read_text())
assert eby["source_files"][shared["path"]] == shared["sha256"]
assert next(c["sha256"] for c in cur["cuts"] if c["path"] == shared["path"]) == shared["sha256"]
for key, pin in m["owner_file_hashes"].items():
    assert sha(repo_path(pin["path"])) == pin["sha256"], key

translation = json.loads(repo_path(m["owners"]["v10"]["translation"]).read_text())
entries = {x["rust_name"].rsplit("::", 1)[-1]: x for x in translation["functions"]
           if "WideExact}::" in x["rust_name"] and x["rust_name"].endswith(("::add", "::from_limbs"))}
assert entries["add"]["source"] == {"file": shared["path"], "begin_line": 81, "end_line": 81}
assert entries["from_limbs"]["source"] == {"file": shared["path"], "begin_line": 207, "end_line": 207}
assert entries["add"]["is_opaque"] and entries["from_limbs"]["is_opaque"]
external = repo_path(m["owners"]["v10"]["external_template"]).read_text()
assert "axiom aspis_core.field.wide_exact.WideExact.add" in external
assert "axiom aspis_core.field.wide_exact.WideExact.from_limbs" in external
# Confirm the accepted implementation owners contain real definitions at the
# corresponding source locations, rather than external axioms.
finish_funs = repo_path(m["owners"]["eby_k_finish"]["lean_function"]).read_text()
current_funs = repo_path(m["owners"]["current_wide"]["lean_function"]).read_text()
assert "def field.wide_exact.WideExact.from_limbs" in finish_funs
assert "lines 207:4-235:5" in finish_funs and all(f"Array.index_usize limbs {i}#usize" in finish_funs for i in range(8))
assert "def field.wide_exact.WideExact.add" in current_funs
assert "lines 81:4-88:5" in current_funs
assert "let q ← field.QM31.add self.c0 rhs.c0" in current_funs
assert "let q1 ← field.QM31.add self.c1 rhs.c1" in current_funs
leanlog = (P / "receipts/compile.log").read_text()
assert "literal_from_limbs_installed" in leanlog and "literal_add_installed" in leanlog and "current_add_body" in leanlog
assert "0  swaps" in leanlog and "6.21 real" in leanlog
print("PASS: source-only receipt/checksums/direct imports and all-Result theorem source")
print("PASS: V10, EbyKFinish and CurrentWide operation owners share the pinned Rust file")
print("PASS: V10 raw external axioms are documented and are not treated as proved equalities")
