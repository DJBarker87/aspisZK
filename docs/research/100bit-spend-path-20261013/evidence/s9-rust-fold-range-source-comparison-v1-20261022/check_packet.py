#!/usr/bin/env python3
"""Verify exact source pins and selected Rust Iterator/Range body equality."""
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent
FILES = {
    "rust_1_89_iterator": ROOT / "source/rust-1.89/library/core/src/iter/traits/iterator.rs",
    "rust_1_89_range": ROOT / "source/rust-1.89/library/core/src/iter/range.rs",
    "rust_1_98_iterator": ROOT / "source/rust-1.98/library/core/src/iter/traits/iterator.rs",
    "rust_1_98_range": ROOT / "source/rust-1.98/library/core/src/iter/range.rs",
}
EXPECTED = {
    "rust_1_89_iterator": "d57130b6a4d3f18f8d28fedf5bd953da80492e2f809813ecd3dba0b3276b99ab",
    "rust_1_89_range": "7d5786221245987c467f6504ed59a1185a561f26258024acb9a65bf4f03dea22",
    "rust_1_98_iterator": "db43b7acc33fca53d85fef3ddea29ec9f8c1e768df428676fe2de160f21d5f6b",
    "rust_1_98_range": "df884a169ec674a8d97312096d195b68f0d1761f4ef282a85450f02b1e4ca079",
}

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def extract(path, context, needle):
    text = path.read_text()
    start = text.index(context)
    pos = text.index(needle, start)
    brace = text.index("{", pos)
    depth = 0
    for i in range(brace, len(text)):
        if text[i] == "{":
            depth += 1
        elif text[i] == "}":
            depth -= 1
            if depth == 0:
                body = text[brace:i + 1]
                return {
                    "line_start": text.count("\n", 0, pos) + 1,
                    "line_end": text.count("\n", 0, i + 1),
                    "normalized_sha256": hashlib.sha256(re.sub(r"\s+", "", body).encode()).hexdigest(),
                    "normalized_body": re.sub(r"\s+", "", body),
                }
    raise ValueError(f"unclosed body {needle} in {path}")

for key, path in FILES.items():
    assert path.is_file(), f"missing {path}"
    actual = sha(path)
    assert actual == EXPECTED[key], (key, actual, EXPECTED[key])

checks = [
    ("Iterator::fold", "fn fold<B, F>(mut self, init: B, mut f: F) -> B"),
    ("RangeIteratorImpl::spec_next", "fn spec_next(&mut self) -> Option<T>"),
    ("Range<usize>::Iterator::next", "fn next(&mut self) -> Option<A>"),
    ("unsigned Step::forward_unchecked", "unsafe fn forward_unchecked(start: Self, n: usize) -> Self"),
]
rows = {}
for label, needle in checks:
    items = {}
    for version in ("rust_1_89", "rust_1_98"):
        if label == "Iterator::fold":
            context = "trait Iterator"
            path = FILES[f"{version}_iterator"]
        elif label == "RangeIteratorImpl::spec_next":
            context = "impl<T: TrustedStep> RangeIteratorImpl for ops::Range<T>"
            path = FILES[f"{version}_range"]
        elif label == "Range<usize>::Iterator::next":
            context = "impl<A: Step> Iterator for ops::Range<A>"
            path = FILES[f"{version}_range"]
        else:
            context = "macro_rules! step_unsigned_methods"
            path = FILES[f"{version}_range"]
        items[version] = extract(path, context, needle)
    assert items["rust_1_89"]["normalized_body"] == items["rust_1_98"]["normalized_body"], label
    rows[label] = {v: {k: val for k, val in item.items() if k != "normalized_body"} for v, item in items.items()}
    rows[label]["equal_normalized_body"] = True

# Check the source-level specialization breadcrumbs used by the finite model.
range89 = FILES["rust_1_89_range"].read_text()
range98 = FILES["rust_1_98_range"].read_text()
for source in (range89, range98):
    assert "unsafe_impl_trusted_step![AsciiChar char i8 i16 i32 i64 i128 isize u8 u16 u32 u64 u128 usize Ipv4Addr Ipv6Addr];" in source
    assert "macro_rules! step_unsigned_methods" in source
    assert "unsafe { start.unchecked_add(n as Self) }" in source
    assert "impl<T: TrustedStep> RangeIteratorImpl for ops::Range<T>" in source

manifest = json.loads((ROOT / "manifest.json").read_text())
assert manifest["rust_sources"]["rust_1_89_source_commit"] == "790f1537507dbdb0da320fbb3b1c1eca3b33c474"
assert manifest["rust_sources"]["rust_1_98_source_commit"] == "14210df0e27ccd7d9e6a05b8085cbd438e4bbc65"
assert manifest["claims"]["binary_or_runtime_refinement_proved"] is False
out = {"schema": "s9-rust-fold-range-source-body-comparison-v1", "source_file_sha256": EXPECTED, "critical_bodies": rows, "claim_limit": manifest["claims"]}
(ROOT / "body-comparison.json").write_text(json.dumps(out, indent=2) + "\n")
print("PASS: all four exact source hashes and four normalized bodies match across the two pinned source snapshots")
