#!/usr/bin/env python3
"""Pin the actual refactored Prefix declarations; retain the previous failed kit unchanged."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[4]
SOURCE_PARENT = "ca5ac5dff7eded50dd37ae3b682aac70b2a3bafb"
PARSER_REV = "0dbcc4dd0f7efa4ddb400746d1f24b98a511aab5"
OLD = "docs/research/100bit-spend-path-20261013/tools/record-parser-extraction-kit/parse-record"
UTILITY = HERE.parent / "public-serializer-extraction-kit/extract.py"
WIRE = "crates/aspis-r1-cost-probe/src/r1_wire.rs"
ADDED = [
    ("validated_type", "pub(crate) struct ValidatedRecord"),
    ("validated_row", "pub(crate) fn row(&self)"),
    ("validated_framed", "pub(crate) fn framed(&self)"),
    ("validated_payload", "pub(crate) fn payload(&self)"),
    ("prefix_type", "pub struct Prefix"),
    ("parse_record_at", "fn parse_record_at<"),
    ("prefix_parse", "pub fn parse(bytes: &'a [u8])"),
    ("prefix_record", "pub fn record(&self, row: u8)"),
    ("prefix_payload", "pub fn payload(&self, row: u8)"),
    ("prefix_validated_record", "pub(crate) fn validated_record(&self, row: u8)"),
]


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def blob(path):
    return subprocess.check_output(["git", "-C", str(REPO), "show", f"{PARSER_REV}:{path}"])


class GitSource:
    def __init__(self, raw):
        self.raw = raw

    def read_bytes(self):
        return self.raw


def outputs():
    # Reuse the audited cutter. Compare all old parser declaration bytes with
    # their retained git pin, then cut the current production Prefix and helper.
    assert UTILITY.read_bytes() == blob(str(UTILITY.relative_to(REPO)))
    spec = importlib.util.spec_from_file_location("exact_cuts", UTILITY)
    utility = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(utility)
    old_manifest = json.loads(blob(OLD + "/source-manifest.json"))
    sources = {item["source_path"]: (REPO / item["source_path"]).read_bytes()
               for item in old_manifest["items"]}
    fragments, cuts = {}, []
    for item in old_manifest["items"]:
        fragment, start, end, first, last = utility.find_item(
            GitSource(sources[item["source_path"]]), item["anchor"])
        assert fragment == blob(OLD + "/" + item["fragment_path"])
        assert sha(fragment) == item["fragment_sha256"]
        # Production file may change outside this reused declaration.
        assert fragment == utility.find_item(GitSource(blob(item["source_path"])), item["anchor"])[0]
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
           + b"\n}\n" + fragments["prefix_type"] + b"\n" + fragments["parse_record_at"] + b"\nimpl<'a> Prefix<'a> {\n"
           + b"\n".join(fragments[n] for n in ["prefix_parse", "prefix_record", "prefix_payload", "prefix_validated_record"])
           + b"\n}\n}\n")
    pins = {"source_parent_revision": SOURCE_PARENT,
            "source_status": "working-tree source bytes pinned below; not represented as clean parent",
            "retained_parser_revision": PARSER_REV, "source_files": {p: sha(b) for p, b in sources.items()},
            "declaration_cuts": cuts, "reused_parser_kit": {"path": OLD,
                "lib_sha256": sha(old_lib), "manifest_sha256": sha(blob(OLD + "/source-manifest.json")),
                "exact_reused_declarations": 18},
            "kit_files": {"Cargo.toml": sha((HERE / "Cargo.toml").read_bytes()), "lib.rs": sha(lib)},
            "generator_sha256": sha(Path(__file__).read_bytes()), "cut_utility_sha256": sha(UTILITY.read_bytes()),
            "scope": "28 exact current declarations, including the new immutable-record helper; 18 prior parser declarations byte-identical; derives retained; C1 conversion explicitly matched; no caller-owned mutable record array",
            "boundary": "Exact declaration-cut pins; source-level Rust refinement, fixed total length and runtime correspondence remain OPEN"}
    assert len(cuts) == 28
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
    print("PASS: 28 exact current cuts, including 18 unchanged parser declarations; source refinement OPEN")


if __name__ == "__main__":
    main()
