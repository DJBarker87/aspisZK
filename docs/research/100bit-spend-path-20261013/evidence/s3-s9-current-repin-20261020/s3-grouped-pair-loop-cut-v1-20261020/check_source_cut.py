from pathlib import Path
import hashlib, json, re

ROOT = Path(__file__).resolve().parents[6]
WEIGHTS = ROOT / "crates/aspis-r1-cost-probe/src/weights.rs"
CUT = ROOT / "docs/research/100bit-spend-path-20261013/lean-candidates/s3-s9-current-repin-20261020/s3-grouped-pair-loop-cut-v1-20261020/input/src/lib.rs"

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def item(text, signature):
    start = text.index(signature)
    brace = text.index("{", start)
    depth = 0
    for i in range(brace, len(text)):
        if text[i] == "{": depth += 1
        elif text[i] == "}":
            depth -= 1
            if depth == 0: return text[start:i+1]
    raise AssertionError(f"unclosed item: {signature}")

def compact(s):
    return re.sub(r"\s+", "", s)

orig = item(WEIGHTS.read_text(), "fn s2_grouped_inactive_pair(")
cut = item(CUT.read_text(), "pub fn s2_grouped_inactive_pair<")

expected = orig
replacements = [
    ("fn s2_grouped_inactive_pair(f:&[u8],low:&[E;16])->E", "pub fn s2_grouped_inactive_pair<E:Copy>(coeff:&[E;64],low:&[E;16],zero:E,add:fn(E,E)->E,mul:fn(E,E)->E,)->E"),
    ("[E::ZERO;12]", "[zero;12]"),
    ("coefficients[group].add(field(f,j))", "add(coefficients[group],coeff[j])"),
    ("pair=E::ZERO", "pair=zero"),
    ("weight=E::ZERO", "weight=zero"),
    ("weight.add(challenge)", "add(weight,challenge)"),
    ("pair.add(coefficients[group].mul(weight))", "add(pair,mul(coefficients[group],weight))"),
]
for old, new in replacements:
    assert old in expected, f"expected source fragment absent: {old}"
    expected = expected.replace(old, new)

assert compact(expected) == compact(cut), "source-cut function differs beyond enumerated parser/op parameters"
report = {
    "status": "PASS",
    "production_source_revision": "b2727acd3",
    "production_weights_sha256": sha(WEIGHTS),
    "cut_source_sha256": sha(CUT),
    "checked_function": "s2_grouped_inactive_pair",
    "checked_preserved_structure": [
        "all three loop bounds and nesting",
        "group and mask table reads",
        "mask-bit branch and branch condition",
        "coefficient/weight/pair update order",
    ],
    "only_adaptations": [
        "field(f,j) input made explicit as coeff[j]",
        "E::ZERO made explicit as zero",
        "E.add/E.mul made explicit as add/mul parameters",
    ],
    "does_not_claim": "Aeneas/Lean refinement or algebraic laws for the explicit operations",
}
Path(__file__).with_name("check-report.json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps(report, indent=2))
