"""Mechanical exact-text binding audit for R278 transitive helper definitions."""
import hashlib, json, pathlib, re
ROOT = pathlib.Path(__file__).resolve().parent
WORK = ROOT.parents[1]
R276 = WORK / ".r21-scratch/r276-private-inverse-leaf-translation/generated/AspisR276PrivateInverseLeaves/Funs.lean"
R276_TYPES = WORK / ".r21-scratch/r276-private-inverse-leaf-translation/generated/AspisR276PrivateInverseLeaves/Types.lean"
R249 = WORK / ".r21-scratch/r249-r110-raw/AspisR249R110Raw.lean"
R156 = WORK / "docs/research/v8-full-view-zk-20260912/lean/AspisR156FullFreeze/FunsCore.lean"
R156_TYPES = WORK / "docs/research/v8-full-view-zk-20260912/lean/AspisR156FullFreeze/Types.lean"
RAW = ROOT / "AspisR278PrivateInverseRaw.lean"
sha_file = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
def text(p): return p.read_text()
def definition(src, name):
    marker = "def " + name
    at = src.index(marker)
    stop = min(p for p in (src.find("\n/--", at), src.find("\nend ", at), src.find("\n#print ", at)) if p >= 0)
    return src[at:stop].strip()
def norm(s): return re.sub(r"\s+", " ", s).strip()
def compare(name, source, target, allowed_replacements=()):
    before = definition(text(source), name)
    after = definition(text(target), name)
    adapted = before
    adaptations = []
    for old, new, expected_count, label in allowed_replacements:
        count = adapted.count(old)
        assert count == expected_count, (name, label, count, expected_count)
        adapted = adapted.replace(old, new)
        adaptations.append({"label": label, "from": old, "to": new, "count": count})
    assert norm(adapted) == norm(after), (name, "definition differs beyond allowed whitespace/adaptations")
    return {"name": name, "source_definition_sha256": hashlib.sha256(before.encode()).hexdigest(),
            "bound_definition_sha256": hashlib.sha256(after.encode()).hexdigest(),
            "whitespace_normalized_equal_after_adaptations": True, "adaptations": adaptations}

comparisons = []
r276_names = text(R276)
r249_names = text(R249)
r156_names = text(R156)
# The existing R249 wrapper qualifies two U32 operations with core.num instead of Std.
comparisons.append(compare("circle_norm.joined_inverse.line_norm.r110_norm.B.sub", R276, R249,
    [("core.num.U32.", "Std.U32.", 2, "R249 existing U32 API qualification")]))
comparisons.append(compare("circle_norm.joined_inverse.line_norm.r110_norm.P110", R276, R249))
for name in ["aspis_core.field.P", "aspis_core.field.reduce_u64", "aspis_core.field.M31.mul",
             "aspis_core.field.square_n_loop.body", "aspis_core.field.square_n_loop",
             "aspis_core.field.square_n", "aspis_core.field.M31.inv"]:
    adapters = [("31#i32", "31#u32", 1, "existing R156 M31.mul shift-count API adaptation")] if name == "aspis_core.field.M31.mul" else []
    comparisons.append(compare(name, R276, R156, adapters))

# Verify selected raw declaration blocks are unchanged as extracted by build_raw.py.
raw_text = text(RAW)
copied = []
for name in ["circle_norm.joined_inverse.line_norm.r110_norm.B.ZERO",
             "circle_norm.joined_inverse.line_norm.r110_norm.B.neg",
             "circle_norm.joined_inverse.line_norm.r110_norm.B.inv"]:
    generated = definition(r276_names, name)
    emitted = definition(raw_text, name)
    assert generated in raw_text, (name, "selected generated def block absent from adapter")
    assert norm(generated) == norm(emitted), name
    copied.append({"name": name, "body_equal_whitespace_normalized": True,
                   "generated_def_sha256": hashlib.sha256(generated.encode()).hexdigest(),
                   "raw_def_sha256": hashlib.sha256(emitted.encode()).hexdigest()})

# Representation layout checks: R276's M31 is an alias for Std.U32, as is R156's;
# R249's private B is also a Std.U32 alias. The R278 file declares no type alias.
def line_containing(p, needle): return next(line.strip() for line in text(p).splitlines() if needle in line)
type_layouts = {
    "R276_M31": line_containing(R276_TYPES, "def aspis_core.field.M31 :="),
    "R156_M31": line_containing(R156_TYPES, "def aspis_core.field.M31 :="),
    "R249_B": line_containing(R249, "def circle_norm.joined_inverse.line_norm.r110_norm.B :="),
    "R278_shadows_B_or_M31_type": bool(re.search(r"^\s*def\s+(circle_norm\..*\.B|aspis_core\.field\.M31)\s*(?::|:=)", raw_text, re.M)),
}
assert type_layouts["R249_B"].endswith("def circle_norm.joined_inverse.line_norm.r110_norm.B := Std.U32")
assert type_layouts["R276_M31"] == "def aspis_core.field.M31 := Std.U32"
assert type_layouts["R156_M31"] == type_layouts["R276_M31"] and not type_layouts["R278_shadows_B_or_M31_type"]

all_helpers = {"R249": sha_file(R249), "R156_FunsCore": sha_file(R156)}
report = {
    "scope": "Mechanical declaration-text binding inventory only; no source-correspondence or semantic claim.",
    "inputs_sha256": {"R276_Funs": sha_file(R276), "R276_Types": sha_file(R276_TYPES),
                       "R249_raw": sha_file(R249), "R156_FunsCore": sha_file(R156),
                       "R156_Types": sha_file(R156_TYPES), "R278_raw": sha_file(RAW)},
    "copied_roots": copied,
    "transitive_helper_comparisons": comparisons,
    "representation_layouts": type_layouts,
    "unresolved_local_helpers": [],
    "external_Aeneas_support_references": ["Aeneas Std wrapping arithmetic and scalar casts", "Result/lift", "massert", "Std range iterator and loop combinators"],
    "body_or_type_replacements_in_root_adapter": 0,
    "compiled": False,
}
(ROOT / "binding-audit.json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps({"comparison_count":len(comparisons),"root_count":len(copied),"unresolved":0},indent=2))
