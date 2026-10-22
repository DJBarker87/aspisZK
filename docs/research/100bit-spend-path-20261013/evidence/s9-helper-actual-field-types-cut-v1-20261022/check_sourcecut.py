from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent
REPO = ROOT.parents[1]

def sha_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()

def sha(path: Path) -> str:
    return sha_bytes(path.read_bytes())

def extract(text: str, marker: str) -> str:
    start = text.index(marker)
    brace = text.index("{", start)
    depth = 0
    in_string = False
    escaped = False
    for pos in range(brace, len(text)):
        ch = text[pos]
        if in_string:
            if escaped:
                escaped = False
            elif ch == "\\":
                escaped = True
            elif ch == '"':
                in_string = False
            continue
        if ch == '"':
            in_string = True
        elif ch == "{":
            depth += 1
        elif ch == "}":
            depth -= 1
            if depth == 0:
                return text[start:pos + 1]
    raise AssertionError(f"unterminated item: {marker}")

pins = json.loads((ROOT / "source-identities.json").read_text())
for rel, pin in pins["cut_files"].items():
    assert sha(ROOT / rel) == pin["sha256"], rel
source_snapshots = {
    "candidate_weights": ROOT / "source-snapshots/weights-candidate.rs",
    "frozen_weights": ROOT / "source-snapshots/weights-frozen.rs",
    "actual_core_field": ROOT / "source-snapshots/field.rs",
    "actual_core_wide_exact": ROOT / "source-snapshots/wide_exact.rs",
    "variant_source": ROOT / "source-snapshots/transport.rs",
}
for key, path in source_snapshots.items():
    assert sha(path) == pins[key]["sha256"], key

candidate = source_snapshots["candidate_weights"]
frozen = source_snapshots["frozen_weights"]
field = source_snapshots["actual_core_field"]
wide = source_snapshots["actual_core_wide_exact"]
transport = source_snapshots["variant_source"]
snap_candidate = candidate
snap_frozen = frozen
assert sha(snap_candidate) == sha(candidate)
assert sha(snap_frozen) == sha(frozen)
assert sha(ROOT / "source-snapshots/field.rs") == sha(field)
assert sha(ROOT / "source-snapshots/wide_exact.rs") == sha(wide)
assert sha(ROOT / "source-snapshots/transport.rs") == sha(transport)

candidate_text = candidate.read_text()
cut_weights = (ROOT / "input/src/weights.rs").read_text()
cut_transport = (ROOT / "input/src/transport.rs").read_text()
candidate_items = {
    "field_90_byte_body": extract(candidate_text, "pub fn field(bytes:&[u8],i:usize)"),
    "factored_s2_libra_weights": extract(candidate_text, "fn factored_s2_libra_weights("),
    "twofold_libra_weights": extract(candidate_text, "fn twofold_libra_weights("),
    "Weights_scalar_factor": extract(candidate_text, "fn scalar_factor(f:&[K;4],p:&[E;4])"),
    "Weights_struct": extract(candidate_text, "pub struct Weights {"),
}
for name, source_text in candidate_items.items():
    pin = pins["snippets"][name]
    assert sha_bytes(source_text.encode()) == pin["sha256"], name
    assert source_text in cut_weights, f"cut changed source item {name}"

projection = pins["snippets"]["S2_projection_statement"]["text"]
assert sha_bytes(projection.encode()) == pins["snippets"]["S2_projection_statement"]["sha256"]
assert cut_weights.count(projection) == 1
for method, pin in pins["opaque_arithmetic_bodies"].items():
    source_key = "actual_core_field" if pin["source_path"].endswith("field.rs") else "actual_core_wide_exact"
    source_path = source_snapshots[source_key]
    assert sha(source_path) == pin["source_file_sha256"], method
    body = pin["method_text"]
    assert body in source_path.read_text(), f"pinned body absent: {method}"
    assert sha_bytes(body.encode()) == pin["method_body_sha256"], method

variant_text = extract(transport.read_text(), "pub enum Variant")
assert sha_bytes(variant_text.encode()) == pins["snippets"]["Variant_enum"]["sha256"]
assert variant_text in cut_transport

assert sha(ROOT / "input/src/field.rs") == pins["actual_core_field"]["sha256"]
assert sha(ROOT / "input/src/field/wide_exact.rs") == pins["actual_core_wide_exact"]["sha256"]
assert (ROOT / "input/src/lib.rs").read_text() == "#![no_std]\npub mod field;\npub mod transport;\npub mod weights;\n"

print("source cut checks: PASS")
