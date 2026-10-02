#!/usr/bin/env python3
"""Deterministically stage four exact R292 prefix-loop blocks with existing bindings."""
from pathlib import Path
import hashlib, json

ROOT = Path(__file__).resolve().parents[1]
OUT = Path(__file__).resolve().parent
SOURCE = ROOT / 'r292-private-batch-translation/generated/AspisR292PrivateBatch/Funs.lean'
INVENTORY = ROOT / 'r315-batch-prefix-loop-inventory/inventory.json'
R249 = ROOT / 'r249-r110-raw/AspisR249R110Raw.lean'
R249_AUDIT = ROOT / 'r249-r110-raw/binding-audit.json'
R316 = ROOT / 'r316-slice-last-raw/AspisR316SliceLastRaw.lean'
R316_AUDIT = ROOT / 'r316-slice-last-raw/binding-audit.json'
TARGET = OUT / 'AspisR318BatchPrefixRaw.lean'
NAMES = [
    'circle_norm.joined_inverse.line_norm.r110_norm.batch_loop0.body',
    'circle_norm.joined_inverse.line_norm.r110_norm.batch_loop0',
    'circle_norm.joined_inverse.line_norm.r110_norm.batch_loop1.body',
    'circle_norm.joined_inverse.line_norm.r110_norm.batch_loop1',
]

def sha(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()

src = SOURCE.read_text()
inv = json.loads(INVENTORY.read_text())
assert len(inv['blocks']) == 4
blocks = []
for name, meta in zip(NAMES, inv['blocks'], strict=True):
    assert meta['lean_name'] == 'AspisR292PrivateBatch.' + name
    marker = 'def ' + name + '\n'
    pos = src.index(marker)
    begin = src.rfind('/--', 0, pos)
    end = src.find('\n/--', pos)
    block = src[begin:end].rstrip() + '\n'
    assert sha(block.encode()) == meta['verbatim_block_sha256'], name
    blocks.append(block)

header = '''import Aeneas.Std
import AspisR249R110Raw
import AspisR316SliceLastRaw
open Aeneas Aeneas.Std Result ControlFlow Error
open AspisR249R110Raw AspisR316SliceLastRaw
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

noncomputable section
namespace AspisR318BatchPrefixRaw

'''
trailer = '\n'.join('#print axioms ' + n for n in NAMES) + '\n\nend AspisR318BatchPrefixRaw\n'
TARGET.write_text(header + '\n'.join(blocks) + '\n' + trailer)

raw249 = R249.read_text()
raw316 = R316.read_text()
assert 'def circle_norm.joined_inverse.line_norm.r110_norm.B.mul\n' in raw249
assert 'def core.slice.Slice.last ' in raw316
r249a = json.loads(R249_AUDIT.read_text())
r316a = json.loads(R316_AUDIT.read_text())

# Check that every direct qualified reference in selected blocks resolves to the
# specified staged bindings or the named Aeneas.Std dependency boundary.
block_text = '\n'.join(blocks)
assert block_text.count('core.slice.Slice.last') == 2
assert block_text.count('circle_norm.joined_inverse.line_norm.r110_norm.B.mul') == 2
assert block_text.count('def ') == 4
assert 'def core.slice.Slice.last' not in block_text
assert 'def circle_norm.joined_inverse.line_norm.r110_norm.B.mul' not in block_text
assert r316a['input_fun_id'] == 12
assert r316a['adapter'] == 'Only generated Usize.sub -> existing UScalar.sub API identifier; the rest of the block is exact'
assert r316a['fresh_types_or_execution_assumptions'] is False
assert 'Std.U32' in raw249 and 'wrapping_mul' in raw249

report = {
  'scope': 'Mechanical raw staging only; no compile, proof, or source-semantics claim.',
  'target': str(TARGET.relative_to(ROOT.parent)),
  'target_sha256': sha(TARGET.read_bytes()),
  'source_revision_recorded': inv['source_revision_recorded'],
  'source_file': str(SOURCE.relative_to(ROOT)),
  'source_sha256': sha(SOURCE.read_bytes()),
  'source_inventory_sha256': sha(INVENTORY.read_bytes()),
  'blocks': [
    {'lean_name': 'AspisR318BatchPrefixRaw.' + n,
     'source_lean_name': 'AspisR292PrivateBatch.' + n,
     'source_verbatim_block_sha256': meta['verbatim_block_sha256'],
     'staged_verbatim_block_sha256': sha(b.encode()),
     'exact': sha(b.encode()) == meta['verbatim_block_sha256'],
     'source_span': meta['rust_source_span']}
    for n, meta, b in zip(NAMES, inv['blocks'], blocks, strict=True)
  ],
  'types': {'B': 'AspisR249R110Raw.circle_norm.joined_inverse.line_norm.r110_norm.B = Std.U32',
            'C': 'existing R249 alias B × B'},
  'bindings': {
    'core.slice.Slice.last': {
      'provider': 'opened AspisR316SliceLastRaw actual emitted definition',
      'target_declaration': 'AspisR316SliceLastRaw.core.slice.Slice.last',
      'source_fun_id': r316a['input_fun_id'],
      'adapter': r316a['adapter'],
      'staged_definition_sha256': sha(R316.read_bytes()),
      'audit_sha256': sha(R316_AUDIT.read_bytes()),
      'no_shadow': True,
      'sole_existing_executable_definition': True,
      'proof_status_note': 'R317 universal proof is a separate root-owned task; no theorem is asserted by this raw staging.',
      'note': 'R316 Lean proof/audit is external campaign evidence; this draft only imports the raw declaration.'
    },
    'B.mul': {
      'provider': 'opened AspisR249R110Raw existing helper',
      'target_declaration': 'AspisR249R110Raw.circle_norm.joined_inverse.line_norm.r110_norm.B.mul',
      'staged_definition_sha256': sha(R249.read_bytes()),
      'audit_sha256': sha(R249_AUDIT.read_bytes()),
      'inherited_word_count_adapter': {'source': 'R249 binding-audit.json replacement_counts', 'exact_replacement': 'Std.U64.wrapping_shr x 31#i32 -> Std.U64.wrapping_shr x 31#u32', 'count': r249a['replacement_counts']['Std.U64.wrapping_shr x 31#i32 -> Std.U64.wrapping_shr x 31#u32'], 'R249_B_mul_source_body_sha256': next(x['source_normalized_sha256'] for x in r249a['selected_body_checks'] if x['name'].endswith('.B.mul'))}
    },
    'other_Aeneas.Std_symbols': ['IteratorSliceIter.next', 'Vec.deref', 'Option.unwrap', 'Vec.push', 'loop',
                                  'Iter', 'Vec', 'Result', 'ControlFlow', 'Slice'],
    'boundary': 'Named Aeneas.Std support dependencies remain imported library symbols; this staging makes no independent claims about them.'
  },
  'attributes_docstrings_and_bodies': 'Exact selected generated blocks retained, including original doc comments and rust_loop_body/rust_loop attributes.',
  'print_axioms': NAMES,
  'compiled': False
}
(OUT / 'binding-audit.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({'target_sha256': report['target_sha256'], 'block_hashes_exact': all(x['exact'] for x in report['blocks']), 'report': str(OUT / 'binding-audit.json')}, indent=2))
