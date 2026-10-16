#!/usr/bin/env python3
"""Extend the exact validator cuts with its actual ASWP encoder caller.

No production source is edited; no callback or external stub is substituted.
The retained cutter and fourteen validation declarations are reused unchanged.
This preparation alone makes no extraction or refinement claim.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[4]
REVISION = "765f30965aa54f042c517a4a31ba6d1c4dd95d40"
OLD = HERE.parent / "withdrawal-validation-extraction-kit"
PAYMENT = "crates/aspis-statement/src/pool_v1/payment_relation.rs"
ADDED = [
    ("m31_to_le_bytes", "crates/aspis-core/src/field.rs", "pub fn to_le_bytes(self)"),
    ("encode_digest", "crates/aspis-statement/src/atomic_statement.rs", "pub fn encode_digest_canonical("),
    ("digest_encoding_version", "crates/aspis-statement/src/pool_v1/format.rs", "pub const POOL_V1_DIGEST_ENCODING_VERSION:"),
    ("transition_kind", "crates/aspis-statement/src/pool_v1/historical_anchor.rs", "pub enum PoolV1TransitionKind"),
    *[(name.lower(), PAYMENT, anchor) for name, anchor in [
        ("STATEMENT_BYTES", "pub const POOL_V1_PAYMENT_STATEMENT_BYTES:"),
        ("STATEMENT_VERSION", "pub const POOL_V1_PAYMENT_STATEMENT_VERSION:"),
        ("WITHDRAWAL_MAGIC", "pub const POOL_V1_WITHDRAWAL_STATEMENT_MAGIC:"),
        *[(name, "const " + name + ":") for name in [
            "POOL_OFFSET", "DEPLOYMENT_DOMAIN_OFFSET", "ANCHOR_SEQUENCE_OFFSET",
            "ANCHOR_ROOT_OFFSET", "NULLIFIER_OFFSET", "ASSET_ID_OFFSET",
            "AMOUNT_OR_RESERVED_OFFSET", "FIRST_OUTPUT_OR_DESTINATION_OFFSET",
            "SECOND_OUTPUT_OFFSET"]],
        ("ENCODE_COMMON", "fn encode_common("),
        ("ENCODE_WITHDRAWAL", "pub fn encode_pool_v1_withdrawal_public_v1("),
    ]],
]


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def git_bytes(path):
    return subprocess.check_output(["git", "-C", str(REPO), "show", f"{REVISION}:{path}"])


def outputs():
    utility = OLD / "extract.py"
    assert utility.read_bytes() == git_bytes(str(utility.relative_to(REPO)))
    spec = importlib.util.spec_from_file_location("validator_cuts", utility)
    cutter = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(cutter)
    previous = json.loads((OLD / "source-manifest.json").read_text())
    fragments, cuts, sources = {}, [], {}
    for name, path, anchor in [*cutter.ITEMS, *ADDED]:
        raw = (REPO / path).read_bytes()
        assert raw == git_bytes(path), path
        sources[path] = sha(raw)
        fragment, start, end, first, last = cutter.find_item(REPO / path, anchor)
        assert raw[start:end] == fragment
        reused = name in {item[0] for item in cutter.ITEMS}
        if reused:
            prior = next(item for item in previous["items"] if item["name"] == name)
            assert fragment == (OLD / prior["fragment_path"]).read_bytes()
            assert sha(fragment) == prior["fragment_sha256"]
        fragments[name] = fragment
        cuts.append({"name": name, "source_path": path, "anchor": anchor,
                     "byte_start": start, "byte_end_exclusive": end,
                     "first_line": first, "last_line": last - 1,
                     "sha256": sha(fragment), "reused_validator_cut": reused})

    out = bytearray(b"// Exact declaration cuts; namespace layout only.\n#![no_std]\n#![allow(dead_code)]\n")
    spans = []

    def emit(name):
        start = len(out)
        out.extend(fragments[name])
        spans.append({"name": name, "byte_start": start, "byte_end_exclusive": len(out)})
        out.extend(b"\n")

    out.extend(b"pub mod aspis_core { pub mod field {\n")
    emit("m31_modulus")
    emit("m31_type")
    out.extend(b"impl M31 {\n")
    emit("m31_to_le_bytes")
    out.extend(b"}\n}}\npub mod poseidon2 { use crate::aspis_core::field::M31;\n")
    emit("digest_elems")
    emit("digest_alias")
    out.extend(b"}\nuse poseidon2::Digest;\n")
    emit("value_limit")
    emit("encode_digest")
    out.extend(b"pub mod pool_v1 {\n")
    for name in ["pool_tree_depth", "leaf_capacity", "digest_encoding_version"]:
        emit(name)
    out.extend(b"pub mod historical_anchor {\n")
    emit("transition_kind")
    out.extend(b"}\npub mod payment_relation {\nuse crate::aspis_core::field::{M31, P};\nuse crate::{poseidon2::Digest, VALUE_LIMIT, encode_digest_canonical};\nuse super::{POOL_V1_LEAF_CAPACITY, POOL_V1_DIGEST_ENCODING_VERSION, historical_anchor::PoolV1TransitionKind};\n")
    for name, _, _ in cutter.ITEMS[7:]:
        emit(name)
    for name, _, _ in ADDED[4:]:
        emit(name)
    out.extend(b"}}\n")
    assert len(spans) == len(cuts) == 32
    manifest = {
        "source_revision": REVISION,
        "source_files": sources,
        "cuts": cuts,
        "rendered_spans": spans,
        "reused_validation_declarations": 14,
        "cut_utility_sha256": sha(utility.read_bytes()),
        "generator_sha256": sha(Path(__file__).read_bytes()),
        "kit_files": {"lib.rs": sha(out), "Cargo.toml": sha((HERE / "Cargo.toml").read_bytes())},
        "scope": "Actual encoder, common encoder, canonical-digest encoder, constants and unchanged validator cone; extraction and source-caller theorem OPEN",
    }
    return {"lib.rs": bytes(out), "source-pins.json": (json.dumps(manifest, indent=2, sort_keys=True) + "\n").encode()}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    for name, content in outputs().items():
        if args.check:
            assert (HERE / name).read_bytes() == content, name
        else:
            (HERE / name).write_bytes(content)
    print("PASS:32 exact source cuts;14 unchanged validation declarations; extraction/refinement OPEN")


if __name__ == "__main__":
    main()
