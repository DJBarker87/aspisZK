#!/usr/bin/env python3
"""Stage the guarded canonical M31 multiplication experiment.

This copies one already validated R19 channel-c stage, checks every file in
its frozen R18 manifest, and edits only the staged core field implementation.
The repository production ``crates/aspis-core/src/field.rs`` is never edited.
"""
import argparse
import hashlib
import json
import shutil
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument("--stage", type=Path, required=True)
parser.add_argument("--output", type=Path, required=True)
args = parser.parse_args()
stage_root = args.stage.resolve()
output_root = args.output.resolve()
assert output_root != stage_root, "output must differ from input stage"
assert stage_root not in output_root.parents, "output must not be nested inside input stage"
assert not output_root.exists(), output_root


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


manifest_path = args.stage / "r18-stage.json"
manifest = json.loads(manifest_path.read_text())
assert manifest.get("profile", "").startswith("AV8/R19/"), manifest.get("profile")
assert "r19_channel" in manifest, "channel-c manifest required"
for name, expected in manifest["files"].items():
    path = args.stage / name
    assert path.is_file(), path
    assert sha256(path) == expected, name

core = args.stage / "crates/aspis-core/src/field.rs"
assert core.is_file(), "stage must contain crates/aspis-core/src/field.rs"
excluded_names = {
    "sbf-primary", "host-c", "wire-controls-c", "logs", "keypair",
    "sbf-primary.log", "host-gate.log", "primary-world0.jsonl",
    "primary-world1.jsonl", "primary-world0.time", "primary-world1.time",
}


def ignore_stale(_directory: str, names: list[str]) -> set[str]:
    return {name for name in names if name in excluded_names or
            name.startswith("sbf-primary") or name.startswith("host-c") or
            name.startswith("wire-controls-c")}


shutil.copytree(args.stage, args.output, ignore=ignore_stale)
staged_core = args.output / "crates/aspis-core/src/field.rs"
before = sha256(staged_core)
old = """    pub fn mul(self, rhs: M31) -> M31 {
        M31(reduce_u64(self.0 as u64 * rhs.0 as u64))
    }"""
new = """    pub fn mul(self, rhs: M31) -> M31 {
        if self.0 < P && rhs.0 < P {
            let x = (self.0 as u64) * (rhs.0 as u64);
            let s = (x & P as u64) + (x >> 31);
            M31(if s >= P as u64 { (s - P as u64) as u32 } else { s as u32 })
        } else {
            M31(reduce_u64(self.0 as u64 * rhs.0 as u64))
        }
    }"""
source = staged_core.read_text()
assert source.count(old) == 1, "unexpected M31::mul source shape"
staged_core.write_text(source.replace(old, new))
after = sha256(staged_core)

checker = Path(__file__).with_name("r19_canonical_check.rs")
shutil.copy2(checker, args.output / checker.name)
manifest["canonical_mul_candidate"] = {
    "before_sha256": before,
    "after_sha256": after,
    "fallback": "original reduce_u64 for any self.0 >= P or rhs.0 >= P",
    "one_fold_bound": "canonical product x <= (P-1)^2; x>>31 <= P-3 and x&P <= P, hence s <= 2P-3 < 2P",
    "checker": checker.name,
    "built": False,
}
manifest["files"].update(
    {
        str(path.relative_to(args.output)): sha256(path)
        for path in (staged_core, args.output / checker.name)
    }
)
(args.output / "r18-stage.json").write_text(json.dumps(manifest, indent=2) + "\n")
print(json.dumps({"stage": str(args.output), "profile": manifest["profile"],
                  "core_before_sha256": before, "core_after_sha256": after,
                  "checker": checker.name, "built": False}))
