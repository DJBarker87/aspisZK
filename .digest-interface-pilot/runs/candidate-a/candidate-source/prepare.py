#!/usr/bin/env python3
"""Generate/check a reversible CANDIDATE interface edit, never production source."""
from pathlib import Path
import argparse
import difflib
import hashlib
import json
import subprocess

HERE = Path(__file__).resolve().parent
REVISION = "b2ad6649de4c1b97c2270a1c8bd4bbfe5537d52c"
SOURCE = "crates/aspis-r1-cost-probe/src/r1_wire.rs"
SOURCE_SHA = "4ce97b7bc11b495dc8af3ef79f29dbbd9ebba7c2427a6db1acb8851759b1d305"
sha = lambda b: hashlib.sha256(b).hexdigest()

def expected():
    source = subprocess.check_output(["git", "show", f"{REVISION}:{SOURCE}"], cwd=HERE)
    assert sha(source) == SOURCE_SHA
    lines = source.decode().splitlines(keepends=True)
    spans = {"error": (23, 36), "transcript": (168, 176), "impl": (178, 178), "method": (194, 208)}
    original = {name: "".join(lines[a-1:b]) for name, (a, b) in spans.items()}
    replacements = {
        "error": [],
        "transcript": [("pub struct SemanticTranscript {", "pub struct SemanticTranscript<H: Digest32> {", 1),
                       ("hash: HashFn,", "hash: H,", 1)],
        "impl": [("impl SemanticTranscript {", "impl<H: Digest32> SemanticTranscript<H> {", 1)],
        "method": [("(self.hash)(", "self.hash.digest(", 3)],
    }
    candidate = {}
    for name, text in original.items():
        changed = text
        for old, new, count in replacements[name]:
            assert changed.count(old) == count, (name, old)
            changed = changed.replace(old, new)
        restored = changed
        for old, new, count in reversed(replacements[name]):
            assert restored.count(new) == count, (name, new)
            restored = restored.replace(new, old)
        assert restored == text, name
        candidate[name] = changed
    trait = "pub trait Digest32: Copy {\n    fn digest(&self, parts: &[&[u8]]) -> [u8; 32];\n}\n"
    preamble = "// CANDIDATE SOURCE: interface feasibility only; not unchanged release Rust.\n#![no_std]\n#![allow(dead_code)]\n"
    lib = (preamble + "pub mod digest {\n" + trait + "}\n\npub mod r1_wire {\n"
           + "use crate::digest::Digest32;\n" + candidate["error"] + "\n"
           + candidate["transcript"] + "\n" + candidate["impl"] + candidate["method"] + "}\n}\n")
    outputs = {
        "lib.rs": lib,
        "Cargo.toml": '[package]\nname = "aspis-r1-digest-interface-candidate"\nversion = "0.0.0"\nedition = "2021"\npublish = false\n\n[lib]\npath = "lib.rs"\n\n[features]\ndefault = []\n\n[workspace]\n',
        "Cargo.lock": '# Dependency-free CANDIDATE kit lockfile.\nversion = 4\n\n[[package]]\nname = "aspis-r1-digest-interface-candidate"\nversion = "0.0.0"\n',
        "original/r1_wire.rs": source.decode(),
        "candidate-interface.patch": "".join(difflib.unified_diff(
            (original["error"] + original["transcript"] + original["impl"] + original["method"] + "}\n").splitlines(keepends=True),
            (trait + candidate["error"] + candidate["transcript"] + candidate["impl"] + candidate["method"] + "}\n").splitlines(keepends=True),
            fromfile="exact-selected-spans", tofile="candidate-selected-spans")),
    }
    for name, text in original.items():
        outputs[f"original/{name}.rs"] = text
    manifest = {
        "classification": "CANDIDATE source; no unchanged-source or release-interface adoption claim",
        "source_revision": REVISION, "source_path": SOURCE, "source_sha256": SOURCE_SHA,
        "cuts": {name: {"lines": list(spans[name]), "original_sha256": sha(original[name].encode()),
                        "candidate_sha256": sha(candidate[name].encode()), "substitutions": replacements[name],
                        "inverse_restores_exact_span": True} for name in spans},
        "candidate_trait": trait,
        "wrappers": "no_std crate and module scopes; original impl closer supplied because unrelated methods are omitted",
        "roots": ["crate::r1_wire::SemanticTranscript::sample_block_validated", "crate::digest::Digest32"],
        "excluded": "constructor, other transcript methods/callers, concrete backend, SDK, parser, fields, Observer",
        "kit_files": {name: sha(text.encode()) for name, text in outputs.items()},
        "prepare_script_sha256": sha(Path(__file__).read_bytes()),
    }
    outputs["source-pins.json"] = json.dumps(manifest, indent=2) + "\n"
    return outputs

if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument("--check", action="store_true")
    args = p.parse_args()
    for name, text in expected().items():
        out = HERE / name
        if args.check:
            assert out.read_bytes() == text.encode(), name
        else:
            out.parent.mkdir(parents=True, exist_ok=True)
            out.write_text(text)
    print("PASS: candidate kit; four exact cuts; inverse substitutions restore every original byte")
