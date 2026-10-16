#!/usr/bin/env python3
"""Exact eight-declaration cut; prepare/check only, never run a compiler."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import textwrap

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[4]
REVISION = "670b7e149f94004baa5b138bdc2db28f3bc646bd"
BASE = "b05c2ceb44320040168efe15e159e5d633a185b5"
FIELD = "crates/aspis-core/src/field.rs"
SAMPLER = "crates/aspis-r1-cost-probe/src/sampler.rs"
CUTS = [
    ("P", FIELD, 18, 19),
    ("M31", FIELD, 21, 23),
    ("CM31", FIELD, 253, 258),
    ("CM31::new", FIELD, 270, 273),
    ("QM31", FIELD, 430, 435),
    ("qm31_div_pass", SAMPLER, 6, 18),
    ("qm31_digits", SAMPLER, 20, 43),
    ("qm31_sample", SAMPLER, 45, 51),
]


def sha(data):
    return hashlib.sha256(data).hexdigest()


def source(revision, path):
    return subprocess.check_output(["git", "-C", str(REPO), "show", f"{revision}:{path}"])


def fragment(raw, first, last):
    return "".join(raw.decode().splitlines(keepends=True)[first - 1:last])


def outputs():
    sources = {path: source(REVISION, path) for _, path, _, _ in CUTS}
    pieces, receipts = {}, []
    for name, path, first, last in CUTS:
        piece = fragment(sources[path], first, last)
        pieces[name] = piece
        receipts.append({"name": name, "path": path, "first_line": first,
                         "last_line": last, "sha256": sha(piece.encode())})
    tests = fragment(sources[SAMPLER], 130, 230)
    old_source = source(BASE, SAMPLER)
    # Preserve the old sampler function body modulo its test-only name/indent.
    old_function = fragment(old_source, 8, 24)
    marker = "    fn old_sample(block: &[u8; 32]) -> QM31 {\n"
    reference = tests[tests.index(marker):tests.index("\n    fn old_pass")].rstrip() + "\n"
    assert textwrap.dedent(reference).replace("fn old_sample", "pub fn qm31_sample", 1) == old_function
    lib = ("// Exact source cuts. cfg(test) adds the pinned production tests only.\n"
           "pub mod field {\n" + pieces["P"] + pieces["M31"] + pieces["CM31"]
           + "impl CM31 {\n" + pieces["CM31::new"] + "}\n" + pieces["QM31"]
           + "}\npub mod sampler {\nuse crate::field::{CM31, M31, P, QM31};\n"
           + pieces["qm31_div_pass"] + pieces["qm31_digits"] + pieces["qm31_sample"]
           + tests + "}\n")
    manifest = {
        "source_revision": REVISION, "before_revision": BASE,
        "source_files": {path: sha(raw) for path, raw in sources.items()},
        "declaration_cuts": receipts,
        "native_test_cut": {"path": SAMPLER, "first_line": 130, "last_line": 230,
                            "sha256": sha(tests.encode()), "cfg": "test only; absent from release LLBC"},
        "old_sampler_reference": {"revision": BASE, "source_sha256": sha(old_source),
                                  "name_indent_only_equality_checked": True},
        "kit_files": {"lib.rs": sha(lib.encode()), "Cargo.toml": sha((HERE / "Cargo.toml").read_bytes())},
        "generator_sha256": sha(Path(__file__).read_bytes()),
        "namespace_only_changes": ["field and sampler module wrappers", "crate::field import", "CM31 impl wrapper"],
        "features": "No dependencies, default features or production cfg; cfg(test) excluded in extraction.",
        "preservation": "Exact cut equality checked; Rust lowering/Aeneas/runtime correspondence remain OPEN.",
        "forbidden": "No M31/CM31/QM31 arithmetic methods; no opaque external replacements.",
    }
    return {"lib.rs": lib, "source-pins.json": json.dumps(manifest, indent=2, sort_keys=True) + "\n"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    for name, data in outputs().items():
        target = HERE / name
        if args.check:
            if target.read_text() != data:
                raise SystemExit("FAIL: exact source cut differs: " + str(target))
        else:
            target.write_text(data)
    print("PASS: eight exact source declarations, exact old reference and cfg(test) module; no refinement claim")


if __name__ == "__main__":
    main()
