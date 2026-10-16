#!/usr/bin/env python3
"""Create the minimal echeck module from the pinned verifier source.

The function declaration/body is copied byte-for-byte. The only surrounding
source is the exact Error enum used by verifier.rs and imports for the exact
field module. This is an extraction cut, not a replacement for View::parse.
"""
from pathlib import Path
import hashlib, json

root = Path(__file__).resolve().parent
src = root / "source-verifier.rs"
s = src.read_text()
EXPECTED_VERIFIER = "b62d50ad47f9f4c736323f54e6d2b90e80fe18d4730d29994febe0ca0756734d"
EXPECTED_FIELD = "28df5a1abee13bde4b3aa9eeceb0489bedf00531f298460954a97661f5f1baea"
EXPECTED_WIDE = "6260fa9d179328714e7df59640abb7a76a326e98900993ce7d3da98c6411d10b"
assert hashlib.sha256(src.read_bytes()).hexdigest() == EXPECTED_VERIFIER
assert hashlib.sha256((root / "input/src/field.rs").read_bytes()).hexdigest() == EXPECTED_FIELD
assert hashlib.sha256((root / "input/src/field/wide_exact.rs").read_bytes()).hexdigest() == EXPECTED_WIDE
needle = "fn echeck(b:&[u8],k:bool)->Result<(),Error> {"
start = s.index(needle)
brace = s.index("{", start)
depth = 0
end = None
for i in range(brace, len(s)):
    if s[i] == "{": depth += 1
    elif s[i] == "}":
        depth -= 1
        if depth == 0:
            end = i + 1
            break
assert end is not None
body = s[start:end]
assert body == "fn echeck(b:&[u8],k:bool)->Result<(),Error> {\n    for c in b.chunks_exact(32) {let x=E::from_le_bytes(c).ok_or(Error::Parse)?;if k&&x.c1()!=K::ZERO {return Err(Error::Parse);}}\n    Ok(())\n}"
out = root / "input/src/verifier.rs"
wrapper = "pub fn echeck_round1(b: &[u8]) -> Result<(), Error> { echeck(b, false) }"
out.write_text("use crate::field::{QM31 as K, WideExact as E};\n\n#[derive(Debug, Clone, Copy, PartialEq, Eq)]\npub enum Error { Parse, Semantic, Transcript, Relation, Merkle, Query, Checkpoint, Allocation }\n\n" + body + "\n\n" + wrapper + "\n")
manifest = {
  "scope": "single helper source cut; no View::parse claim",
  "package_name": "aspis-r1-mask-extraction-probe",
  "expected_aeneas_namespace": "AspisR1SelectedMaskProbe",
  "original_source": "crates/aspis-r1-cost-probe/src/verifier.rs",
  "original_sha256": hashlib.sha256(s.encode()).hexdigest(),
  "preserved_source_copy_sha256": hashlib.sha256(src.read_bytes()).hexdigest(),
  "function": "fn echeck(b:&[u8],k:bool)->Result<(),Error>",
  "function_original_line_range_1based": [32, 35],
  "function_bytes_sha256": hashlib.sha256(body.encode()).hexdigest(),
  "isolated_verifier_module_sha256": hashlib.sha256(out.read_bytes()).hexdigest(),
  "cargo_lock_sha256": hashlib.sha256((root / "input/Cargo.lock").read_bytes()).hexdigest(),
  "cargo_manifest_sha256": hashlib.sha256((root / "input/Cargo.toml").read_bytes()).hexdigest(),
  "function_bytes_exact_match": body == s[start:end],
  "extraction_wrapper": wrapper,
  "wrapper_role": "reachability root specializing the exact source echeck helper at k=false, as used for round1",
  "supporting_error_enum_source": "same original file, Error declaration lines 19-20",
  "field_sources": {
    "crates/aspis-core/src/field.rs": hashlib.sha256((root / "input/src/field.rs").read_bytes()).hexdigest(),
    "crates/aspis-core/src/field/wide_exact.rs": hashlib.sha256((root / "input/src/field/wide_exact.rs").read_bytes()).hexdigest()
  },
  "features": [],
  "wrapper_or_body_edits": "No echeck body edits. The isolated Rust module contains exact echeck declaration/body, the copied Error enum, and a separate echeck_round1 reachability wrapper; crate module wiring is extraction scaffold.",
  "source_pin_assertions": "pass"
}
(root / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
print(json.dumps(manifest, indent=2))
