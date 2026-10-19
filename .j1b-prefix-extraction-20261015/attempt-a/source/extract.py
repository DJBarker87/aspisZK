#!/usr/bin/env python3
"""Pin an exact Prefix extension of the retained parser cut; no builds."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[4]
REV = "0dbcc4dd0f7efa4ddb400746d1f24b98a511aab5"
OLD = "docs/research/100bit-spend-path-20261013/tools/record-parser-extraction-kit/parse-record"
UTILITY = HERE.parent / "public-serializer-extraction-kit/extract.py"
WIRE = "crates/aspis-r1-cost-probe/src/r1_wire.rs"
ADDED = [
    ("validated_type", "pub(crate) struct ValidatedRecord"),
    ("validated_row", "pub(crate) fn row(&self)"),
    ("validated_framed", "pub(crate) fn framed(&self)"),
    ("validated_payload", "pub(crate) fn payload(&self)"),
    ("prefix_type", "pub struct Prefix"),
    ("prefix_parse", "pub fn parse(bytes: &'a [u8])"),
    ("prefix_record", "pub fn record(&self, row: u8)"),
    ("prefix_payload", "pub fn payload(&self, row: u8)"),
    ("prefix_validated_record", "pub(crate) fn validated_record(&self, row: u8)"),
]


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def blob(path):
    return subprocess.check_output(["git", "-C", str(REPO), "show", f"{REV}:{path}"])


class GitSource:
    def __init__(self, raw):
        self.raw = raw

    def read_bytes(self):
        return self.raw


def outputs():
    # Reuse the audited lexical cutter, but supply exact git bytes, never the
    # older production checkout in this independent worker's worktree.
    assert UTILITY.read_bytes() == blob(str(UTILITY.relative_to(REPO)))
    spec = importlib.util.spec_from_file_location("exact_cuts", UTILITY)
    utility = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(utility)
    old_manifest = json.loads(blob(OLD + "/source-manifest.json"))
    sources = {item["source_path"]: blob(item["source_path"])
               for item in old_manifest["items"]}
    fragments, cuts = {}, []
    for item in old_manifest["items"]:
        fragment, start, end, first, last = utility.find_item(
            GitSource(sources[item["source_path"]]), item["anchor"])
        assert fragment == blob(OLD + "/" + item["fragment_path"])
        assert sha(fragment) == item["fragment_sha256"]
        assert sha(sources[item["source_path"]]) == item["source_sha256"]
        cuts.append({"name": item["name"], "path": item["source_path"],
                     "first_line": first, "last_line": last - 1,
                     "sha256": sha(fragment), "reused_exactly": True})
    for name, anchor in ADDED:
        fragment, start, end, first, last = utility.find_item(GitSource(sources[WIRE]), anchor)
        fragments[name] = fragment
        cuts.append({"name": name, "path": WIRE, "first_line": first,
                     "last_line": last - 1, "sha256": sha(fragment), "reused_exactly": False})
    old_lib = blob(OLD + "/lib.rs")
    assert old_lib.endswith(b"}\n")
    lib = (old_lib[:-2] + fragments["validated_type"] + b"\nimpl<'a> ValidatedRecord<'a> {\n"
           + b"\n".join(fragments[n] for n in ["validated_row", "validated_framed", "validated_payload"])
           + b"\n}\n" + fragments["prefix_type"] + b"\nimpl<'a> Prefix<'a> {\n"
           + b"\n".join(fragments[n] for n in ["prefix_parse", "prefix_record", "prefix_payload", "prefix_validated_record"])
           + b"\n}\n}\n")
    pins = {"source_revision": REV, "source_files": {p: sha(b) for p, b in sources.items()},
            "declaration_cuts": cuts, "reused_parser_kit": {"path": OLD,
                "lib_sha256": sha(old_lib), "manifest_sha256": sha(blob(OLD + "/source-manifest.json")),
                "exact_reused_declarations": 18},
            "kit_files": {"Cargo.toml": sha((HERE / "Cargo.toml").read_bytes()), "lib.rs": sha(lib)},
            "generator_sha256": sha(Path(__file__).read_bytes()), "cut_utility_sha256": sha(UTILITY.read_bytes()),
            "scope": "27 exact declarations; original bodies, derives and both Prefix unwraps retained; only namespace/impl wrappers added",
            "boundary": "Preparation pins only; extraction, Rust refinement, fixed total length and runtime correspondence remain OPEN"}
    assert len(cuts) == 27
    return {"lib.rs": lib, "source-pins.json": (json.dumps(pins, indent=2, sort_keys=True) + "\n").encode()}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    for name, raw in outputs().items():
        if args.check:
            assert (HERE / name).read_bytes() == raw, name
        else:
            (HERE / name).write_bytes(raw)
    print("PASS: 27 exact cuts, including 18 unchanged parser declarations; source refinement OPEN")


if __name__ == "__main__":
    main()
