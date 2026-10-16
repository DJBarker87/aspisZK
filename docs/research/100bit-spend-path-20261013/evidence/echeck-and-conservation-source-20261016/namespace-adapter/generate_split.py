#!/usr/bin/env python3
"""Deterministically split the pinned echeck Aeneas output into a private module universe.
The only generated-code transformations are module imports/namespaces and the reuse
adapter for the standard Option.ok_or model; declaration bodies are retained verbatim.
"""
from pathlib import Path
import hashlib, json

ROOT = Path('/tmp/r1-echeck-cut-20261016-results/attempt-a/output/generated/AspisR1SelectedMaskProbe')
OUT = Path('/tmp/AspisR1EcheckCut')
PINS = {
    'Types.lean': '808450d37ed8ef370b6c65a140c884f2e543b898f10072497686b7b10abaffd1',
    'Funs.lean': '6f1b95d2f041f43a5ec36960df3a4123fa4f05e3c51d75f32f4fe5ce2ea22e98',
    'FunsExternal_Template.lean': '6962c00726a9b461860d088a944773e0e68f7e50710cba8a699707c12b99cfe1',
}

def sha(b): return hashlib.sha256(b).hexdigest()
def replace_once(data: bytes, old: bytes, new: bytes, label: str) -> bytes:
    n = data.count(old)
    if n != 1:
        raise SystemExit(f'{label}: expected one occurrence, found {n}')
    return data.replace(old, new, 1)

raw = {}
for name, expected in PINS.items():
    data = (ROOT / name).read_bytes()
    actual = sha(data)
    if actual != expected:
        raise SystemExit(f'{name}: source pin mismatch {actual} != {expected}')
    raw[name] = data

# Keep the entire generated type set, including the exact field and Error carriers.
types = replace_once(raw['Types.lean'], b'namespace AspisR1SelectedMaskProbe',
                     b'namespace AspisR1EcheckCut', 'Types namespace open')
types = replace_once(types, b'end AspisR1SelectedMaskProbe',
                     b'end AspisR1EcheckCut', 'Types namespace close')

# Keep all generated functions, including the complete actual echeck loop and caller.
funs = replace_once(raw['Funs.lean'], b'import AspisR1SelectedMaskProbe.Types',
                    b'import AspisR1EcheckCut.Types', 'Funs Types import')
funs = replace_once(funs, b'import AspisR1SelectedMaskProbe.FunsExternal',
                    b'import AspisR1EcheckCut.FunsExternal', 'Funs external import')
funs = replace_once(funs, b'namespace AspisR1SelectedMaskProbe',
                    b'namespace AspisR1EcheckCut', 'Funs namespace open')
funs = replace_once(funs, b'end AspisR1SelectedMaskProbe',
                    b'end AspisR1EcheckCut', 'Funs namespace close')

# Reuse the already checked prefix parser's explicit Option.ok_or definition
# instead of retaining this extraction's opaque standard-library template.
ext = raw['FunsExternal_Template.lean']
ext = replace_once(ext, b'import AspisR1SelectedMaskProbe.Types',
                  b'import AspisR1EcheckCut.Types', 'External Types import')
ext = replace_once(ext, b'open AspisR1SelectedMaskProbe',
                  b'open AspisR1EcheckCut', 'External open namespace')
old_axiom = b'''axiom core.option.Option.ok_or\n  {T : Type} {E : Type} : Option T \xe2\x86\x92 E \xe2\x86\x92 Result (core.result.Result T E)'''
new_def = b'''def core.option.Option.ok_or\n  {T : Type} {E : Type} (self : Option T) (err : E) : Result (core.result.Result T E) :=\n  AspisR1PrefixAggregateParser.core.option.Option.ok_or self err'''
# Prefix module is imported once as the checked reusable model.
ext = replace_once(ext, b'import AspisR1EcheckCut.Types',
                  b'import AspisR1EcheckCut.Types\nimport AspisR1PrefixAggregateParser.Funs',
                  'External prefix-model import')
ext = replace_once(ext, old_axiom, new_def, 'Option.ok_or model adapter')

(OUT / 'Types.lean').write_bytes(types)
(OUT / 'Funs.lean').write_bytes(funs)
(OUT / 'FunsExternal.lean').write_bytes(ext)
manifest = {
  'status': 'source-only deterministic split; not compiled',
  'raw_generated_inputs': {k: {'path': str(ROOT/k), 'sha256': PINS[k]} for k in PINS},
  'generated_outputs': {k: {'path': str(OUT/k), 'sha256': sha((OUT/k).read_bytes())} for k in ['Types.lean','Funs.lean','FunsExternal.lean']},
  'transformations': [
    'Types: only namespace AspisR1SelectedMaskProbe -> AspisR1EcheckCut; every declaration retained.',
    'Funs: only imported split module names and namespace AspisR1SelectedMaskProbe -> AspisR1EcheckCut; every generated declaration/body retained, including echeck_loop/echeck/echeck_round1.',
    'FunsExternal: imported Types name and open namespace adapted; generated opaque core.option.Option.ok_or template is replaced by a typed definition delegating to AspisR1PrefixAggregateParser.core.option.Option.ok_or.',
    'No generated declaration body was edited or omitted in Types/Funs. The only external-template implementation is the explicitly pinned reusable Option.ok_or model.'
  ],
  'option_ok_or_reuse': {
    'rust_source_path': 'rustc/library/core/src/option.rs:1334-1342',
    'rust_source_sha256': '7cf61204b05d98a95bc2e322d5fbfc1f4f91505109971917d9a7fb47151c50e6',
    'lean_model_path': '/Users/dominic/ZK/.worktrees/100bit-spend-path/docs/research/100bit-spend-path-20261013/lean/extracted-prefix-aggregate-20261016/AspisR1PrefixAggregateParser/Funs.lean',
    'lean_model_sha256': '4e04e86392953c0aabc037cff0e19630a06267c59874aeba6a6391743dee433a',
    'target': 'AspisR1PrefixAggregateParser.Funs',
    'source_revision': 'b38b1ce770f91a86315a3de1f750fbe993389569',
    'olean_sha256': 'b8db9df9bd37656faeccf3464f411ec6611842bc66baee7b636c83af7ef27e42',
    'receipt_path': '/Users/dominic/ZK/.worktrees/100bit-spend-path/docs/research/100bit-spend-path-20261013/evidence/r18-prefix-aggregate-extraction-20261016/lean/runs/funs-a/receipt.json',
    'receipt_sha256': '910c8b7a84d70d3e6dc7ae780903477ea95bc9bad38b84656513cee514023a58',
    'note': 'Explicit Lean model; not this echeck Charon extraction. Used once by adapter.'
  },
  'rust_source_pins': {
    'verifier.rs_sha256': 'b62d50ad47f9f4c736323f54e6d2b90e80fe18d4730d29994febe0ca0756734d',
    'field.rs_sha256': '28df5a1abee13bde4b3aa9eeceb0489bedf00531f298460954a97661f5f1baea',
    'field/wide_exact.rs_sha256': '6260fa9d179328714e7df59640abb7a76a326e98900993ce7d3da98c6411d10b',
    'source_locations': {'verifier.echeck': 'src/verifier.rs:6-9', 'verifier.echeck_round1': 'src/verifier.rs:11', 'WideExact': 'src/field/wide_exact.rs:28-31', 'WideExact.from_limbs': 'src/field/wide_exact.rs:207-235', 'WideExact.from_le_bytes': 'src/field/wide_exact.rs:255-270'},
    'generated_locations': {'WideExact_type': 'Types.lean:37-42', 'from_limbs': 'Funs.lean:40-89', 'from_le_bytes': 'Funs.lean:91-155', 'echeck_loop': 'Funs.lean:204-232', 'echeck': 'Funs.lean:234-239', 'echeck_round1': 'Funs.lean:241-248'}
  },
  'translation_pins': {
    'attempt_manifest_sha256': 'aa6d4ed527c299807bb0390d4a141e4b9e66ea36bc354e40db10cce7b5f481fb',
    'llbc_sha256': '64498c11e0b11b87a40695611a39302d5dfa579cb37a9b05a21d8c8317e3f24e',
    'translation_json_sha256': 'da22030afa27633f50e2cf5ce477aedb3cd5cc53b88a4aeeb7ed4796dfd1344a',
    'rust_verifier_source_sha256': 'b62d50ad47f9f4c736323f54e6d2b90e80fe18d4730d29994febe0ca0756734d'
  }
}
(OUT / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
print(json.dumps(manifest['generated_outputs'], indent=2))
