#!/usr/bin/env python3
"""Rebuild exact current Prepared source cuts using the retained extraction layout.
Only the synthetic entry wrapper changes to supply current caller-owned scratch.
All production cuts are copied by the retained generator, never rewritten.
"""
from pathlib import Path
import argparse, hashlib, importlib.util, json, subprocess, sys
root = Path(__file__).resolve().parents[5]
base = root / "docs/research/100bit-spend-path-20261013/tools/prepared-actual-extraction-kit"
ap = argparse.ArgumentParser()
ap.add_argument("--revision", required=True)
ap.add_argument("--out", type=Path, required=True)
a = ap.parse_args()
ref = subprocess.check_output(["git", "-C", str(root), "rev-parse", a.revision], text=True).strip()
spec = importlib.util.spec_from_file_location("prepared_source", base / "prepare.py")
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
m.REV = ref
sys.argv = [str(base / "prepare.py"), "--base-kit", str(base / "input/base52"), "--out", str(a.out)]
m.main()
p = a.out / "lib.rs"
before = p.read_text()
old = "pub fn prepared_entry<H:crate::aspis_core::Digest32>(sem:&crate::r1_semantic::Verified<H>,v:&crate::verifier::View<'_>,hash:H)->Result<alloc::boxed::Box<crate::verifier::Prepared>,crate::verifier::Error>{crate::verifier::Prepared::new(sem,v,hash)}"
new = "pub fn prepared_entry<H:crate::aspis_core::Digest32>(sem:&crate::r1_semantic::Verified<H>,v:&crate::verifier::View<'_>,hash:H,g:&mut [crate::aspis_core::field::WideExact;29])->Result<alloc::boxed::Box<crate::verifier::Prepared>,crate::verifier::Error>{crate::verifier::Prepared::new(sem,v,hash,g)}"
assert before.count(old) == 1
lib = before.replace(old, new)
# The retained generic item scanner walks backward over lines starting #[.
# The preceding Error's inline cfg variant is not a standalone attribute;
# scanning it into the Phase item duplicates that Error tail in the kit.
phase_path = a.out / "fragments/phase.rs"
old_phase = phase_path.read_text()
raw = subprocess.check_output(["git", "-C", str(root), "show", ref + ":crates/aspis-r1-cost-probe/src/verifier.rs"])
anchor = "#[derive(Debug,Clone,Copy,PartialEq,Eq)]\npub enum Phase"
assert raw.count(anchor.encode()) == 1
start = raw.index(anchor.encode())
end = raw.index(b"}", start) + 1
phase = raw[start:end]
assert b"{" not in phase[phase.index(b"{")+1:]
assert lib.count(old_phase) == 1
lib = lib.replace(old_phase, phase.decode())
phase_path.write_bytes(phase)
# Only Prepared is selected. The unrelated semantic verify caller now calls
# split helpers absent from the historical layout; omit that unselected item
# instead of inventing behavior for its new helpers.
unselected = (a.out / "fragments/verify_observed.rs").read_text()
assert lib.count(unselected) == 1
lib = lib.replace(unselected, "")
p.write_text(lib)
sha = lambda b: hashlib.sha256(b).hexdigest()
pins_path = a.out / "source-pins.json"
pins = json.loads(pins_path.read_text())
pins["kit_files"]["lib.rs"] = sha(p.read_bytes())
pins["kit_files"]["fragments/phase.rs"] = sha(phase)
phase_cut = next(c for c in pins["cuts"] if c["name"] == "phase")
phase_cut.update(start_byte=start, end_byte_exclusive=end, start_line=raw[:start].count(b"\n")+1, end_line_exclusive=raw[:end].count(b"\n")+2, sha256=sha(phase))
pins["excluded_unselected_source_cut"] = next(c for c in pins["cuts"] if c["name"] == "verify_observed")
pins["cuts"] = [c for c in pins["cuts"] if c["name"] != "verify_observed"]
pins["scope"] = "Exact current Prepared::new and prepared_claim source cuts, over retained historical canonical52 carriers and explicit opaque child boundaries. Synthetic entry forwards caller-owned gamma scratch. No claim of current whole-carrier correspondence, body proof, production Rust name resolution, or runtime preservation."
pins["classification"] = "CANDIDATE current source extraction input; old base52 carrier source and child boundaries remain explicit."
pins["generator_provenance"] = {"retained_generator_sha256":sha((base/"prepare.py").read_bytes()), "current_generator_sha256":sha(Path(__file__).read_bytes()), "synthetic_entry_before":old, "synthetic_entry_after":new, "phase_cut_repair":"Exclude preceding inline cfg enum variants from the exact Phase item; original failed input retained in run snapshot."}
pins_path.write_text(json.dumps(pins, indent=2, sort_keys=True)+"\n")
print(json.dumps({"source_revision":ref,"lib_sha256":pins["kit_files"]["lib.rs"],"cuts":len(pins["cuts"]),"classification":pins["classification"]}))
