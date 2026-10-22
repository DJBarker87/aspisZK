from pathlib import Path
import hashlib, json

ROOT = Path(__file__).resolve().parent
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
manifest = json.loads((ROOT / "manifest.json").read_text())
assert manifest["schema"] == "source-cut-evidence-packet-v1"
for rel, expected in manifest["files"].items():
    p = ROOT / rel
    assert p.is_file(), rel
    assert sha(p) == expected, rel

# Exact source identity against both the current checkout and the retained S1
# extraction input.
repo = ROOT.parents[4]
pins = json.loads((ROOT / "source-identities.json").read_text())
for key, rel in (("actual_core_field", "input/src/field.rs"),
                 ("actual_core_wide_exact", "input/src/field/wide_exact.rs")):
    assert sha(ROOT / rel) == pins[key]["sha256"]
    assert sha(repo / pins[key]["path"]) == pins[key]["sha256"]

llbc = json.loads((ROOT / "runs-charon/helper-projection.llbc").read_text())
assert llbc.get("has_errors") is False
assert len(llbc["translated"]["fun_decls"]) == 188
assert len(llbc["translated"]["type_decls"]) == 60
expected = {
    8: (178, 186, "617f4bfe9aaaabf3129ada726faaf601dfac8e1d978eb62ba007dcc6032fdf9f"),
    9: (190, 198, "5e7bdbf0090b8501ebfb42f18e59eec33de255c439d40296787301df2736eb69"),
    10: (81, 88, "711892452ab80cd1a37abcdd41e42375b86d82b577586567da82c5eacadf0f4f"),
    11: (112, 126, "47c8044c02a35cb46e284c30597906a748a2e8904b3ed811189c5f19855b3462"),
}
decls = {d["def_id"]: d for d in llbc["translated"]["fun_decls"] if isinstance(d, dict)}
for ident, (start, end, body_hash) in expected.items():
    meta = decls[ident]["item_meta"]
    span = meta["span"]["data"]
    assert span["beg"]["line"] == start and span["end"]["line"] == end
    assert meta["opacity"] == "Opaque"
    assert hashlib.sha256(meta["source_text"].encode()).hexdigest() == body_hash

owner_map = json.loads((ROOT / "wide-exact-owner-map.json").read_text())
assert owner_map["classification"] == "read-only exact-source comparison; not a Lean refinement theorem"
assert len(owner_map["method_comparisons"]) == 4

for phase in ("charon", "aeneas"):
    r = json.loads((ROOT / f"runs-{phase}/receipt.json").read_text())
    assert r["exit_status"] == 0 and r["timed_out"] is False
    assert r["limits"] == {"memory.high": "2147483648", "memory.max": "4294967296", "memory.swap.max": "0"}
    assert r["swap_current_bytes"] == 0 and "oom_kill 0" in r["memory_events_after"]
    assert r["cgroup"] and r["argv"]

for p in ROOT.rglob("*"):
    if p.is_dir():
        assert p.name != "__pycache__", p
    elif p.suffix in (".pyc", ".olean", ".ilean"):
        raise AssertionError(f"compiled/cache artifact in evidence packet: {p}")

print("attempt7 source-cut packet checks: PASS")
