#!/usr/bin/env python3
"""Audit the R136 frozen-source extraction and source-matrix bridge."""
import hashlib
import json
from pathlib import Path

root = Path(__file__).parents[1]
ev = root / "evidence/r136-before-ood-source"
manifest = json.loads((root / "tools/r136-release-manifest.json").read_text())
receipt = json.loads((ev / "receipt.json").read_text())
pins = json.loads((ev / "source-pins.json").read_text())
command = json.loads((ev / "command.json").read_text())

def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

assert manifest["status"] == receipt["status"] == "PASS"
assert manifest["base_revision"] == receipt["base_revision"]
assert manifest["selected_callback_sha256"] == receipt["selected_callback_sha256"]
for rel, expected in manifest["artifacts"].items():
    assert digest(ev / rel) == expected, rel
for pin in pins.values():
    assert digest(ev / pin["path"]) == pin["sha256"], pin["path"]
target = manifest["targets"][0]
lean = root / "lean" / (target["target"] + ".lean")
assert digest(lean) == target["sha256"]
assert "theorem assigned_eq_source_matrix" in lean.read_text()
funs = (ev / "generated/AspisR136BeforeOod/Funs.lean").read_text()
extern_funs = (ev / "generated/AspisR136BeforeOod/FunsExternal_Template.lean").read_text()
extern_types = (ev / "generated/AspisR136BeforeOod/TypesExternal_Template.lean").read_text()
assert "def before_ood" in funs and "Source: '../relation_callback.rs', lines 120:0-125:1" in funs
assert extern_funs.count("\naxiom ") == 10
assert extern_types.count("\naxiom ") == 1
assert receipt["generated"] == {
    "local_before_ood": True,
    "external_type_templates": 1,
    "external_function_templates": 10,
}
assert receipt["extraction"]["exit"] == receipt["translation"]["exit"] == receipt["lean"]["exit"] == 0
assert receipt["extraction"]["swap"] == receipt["translation"]["swap"] == receipt["lean"]["swap"] == 0
assert "MemorySwapMax=0" in " ".join(command["extract"]["runner"])
assert "crate::before_ood" in command["extract"]["command"]
assert receipt["claims"]["rust_source_execution_bridge"] == "OPEN"
assert receipt["claims"]["actual_sampler_admissibility"] == "OPEN"
assert not receipt["claims"]["privacy"] and not receipt["claims"]["soundness"]
print(json.dumps({"status":"PASS","source_body":"EXTRACTED",
                  "external_layer":"OPEN","privacy":False,"soundness":False}))
