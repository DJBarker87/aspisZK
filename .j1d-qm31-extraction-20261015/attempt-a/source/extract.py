#!/usr/bin/env python3
"""Prepare/check an exact declaration cut; never compile or claim refinement."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[4]
REVISION = "c111cbbf23b3a0f6ed5bebe75c72fe3089fe5be8"
FIELD = "crates/aspis-core/src/field.rs"
SAMPLER = "crates/aspis-r1-cost-probe/src/sampler.rs"
CUTS = [
    ("P", FIELD, 18, 19),
    ("M31", FIELD, 21, 23),
    ("CM31", FIELD, 253, 258),
    ("CM31::new", FIELD, 270, 273),
    ("QM31", FIELD, 430, 435),
    ("qm31_sample", SAMPLER, 6, 24),
]


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def source(path):
    return subprocess.check_output(["git", "-C", str(REPO), "show", f"{REVISION}:{path}"])


def outputs():
    sources = {path: source(path) for _, path, _, _ in CUTS}
    fragments = {}
    receipts = []
    for name, path, first, last in CUTS:
        lines = sources[path].decode().splitlines(keepends=True)
        fragment = "".join(lines[first - 1:last])
        fragments[name] = fragment
        receipts.append({"name": name, "path": path, "first_line": first,
                         "last_line": last, "sha256": sha(fragment.encode())})
    # Original declarations and derives are byte-for-byte cuts. Only namespace,
    # import and impl wrappers are supplied. No loop, index or unwrap rewrite.
    lib = ("// Exact declaration-cut kit; no source-refinement theorem.\n"
           "pub mod field {\n" + fragments["P"] + fragments["M31"] + fragments["CM31"]
           + "impl CM31 {\n" + fragments["CM31::new"] + "}\n" + fragments["QM31"]
           + "}\npub mod sampler {\nuse crate::field::{CM31, M31, P, QM31};\n"
           + fragments["qm31_sample"] + "}\n")
    manifest = {
        "source_revision": REVISION,
        "source_files": {path: sha(raw) for path, raw in sources.items()},
        "declaration_cuts": receipts,
        "kit_files": {"lib.rs": sha(lib.encode()), "Cargo.toml": sha((HERE / "Cargo.toml").read_bytes())},
        "generator_sha256": sha(Path(__file__).read_bytes()),
        "namespace_only_changes": ["Selected original field declarations enclosed in crate::field",
                                   "Original CM31::new enclosed in an impl wrapper",
                                   "Exact sampler function imports the selected crate::field names"],
        "features": "No external dependencies; no source cfg occurs in the selected declarations. This is not a release build.",
        "extraction_status": "PREPARED_ONLY; no Charon/Aeneas run or generated function claimed",
        "preservation": "Declaration selection, Rust/Charon lowering, Aeneas translation and runtime correspondence remain OPEN",
        "runtime_selection": "OPEN for lead selection; local dependencies do not select a release runtime",
    }
    return {"lib.rs": lib, "source-pins.json": json.dumps(manifest, indent=2, sort_keys=True) + "\n"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    for name, text in outputs().items():
        path = HERE / name
        if args.check:
            if path.read_text() != text:
                raise SystemExit("FAIL: source cut/pin differs: " + str(path))
        else:
            path.write_text(text)
    print("PASS: six exact declaration cuts; preparation only; source refinement OPEN")


if __name__ == "__main__":
    main()
