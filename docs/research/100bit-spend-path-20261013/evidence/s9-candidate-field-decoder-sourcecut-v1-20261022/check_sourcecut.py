from pathlib import Path
import hashlib, json, re

ROOT = Path(__file__).resolve().parent
pins = json.loads((ROOT / 'source-pins.json').read_text())
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
for rel in ('input/Cargo.toml', 'input/Cargo.lock', 'input/src/lib.rs', 'input/src/field.rs', 'input/src/field/wide_exact.rs', 'source-snapshots/weights-candidate.rs', 'source-snapshots/weights-frozen.rs'):
    assert sha(ROOT / rel) == pins[rel]['sha256'], rel
rx = re.compile(r'pub fn field\(bytes:&\[u8\],i:usize\)->E \{ E::from_le_bytes\(&bytes\[i\*32\.\.\(i\+1\)\*32\]\)\.unwrap\(\) \}')
def field_body(path):
    m = rx.search(path.read_text())
    assert m, f'missing pinned field declaration in {path}'
    return m.group(0).encode()
candidate = ROOT / 'source-snapshots/weights-candidate.rs'
frozen = ROOT / 'source-snapshots/weights-frozen.rs'
assert sha(candidate) == pins['candidate_weights']['sha256']
assert sha(frozen) == pins['frozen_weights']['sha256']
body = field_body(candidate)
assert body == field_body(frozen)
assert len(body) == pins['field_body']['bytes'] == 90
assert hashlib.sha256(body).hexdigest() == pins['field_body']['sha256']
shim_body = field_body(ROOT / 'input/src/lib.rs')
assert shim_body == body
for rel, key in [('input/src/field.rs', 'aspis_core_field'), ('input/src/field/wide_exact.rs', 'aspis_core_wide_exact')]:
    assert sha(ROOT / rel) == pins[key]['sha256']
for rel, marker in [('input/src/field.rs', 'mod wide_exact;'), ('input/src/field/wide_exact.rs', 'pub fn from_le_bytes(bytes: &[u8]) -> Option<Self>'), ('input/src/field/wide_exact.rs', 'pub fn from_limbs(limbs: [u32; Self::LIMB_COUNT]) -> Option<Self>')]:
    assert marker in (ROOT / rel).read_text(), (rel, marker)
print('source cut checks: PASS')
