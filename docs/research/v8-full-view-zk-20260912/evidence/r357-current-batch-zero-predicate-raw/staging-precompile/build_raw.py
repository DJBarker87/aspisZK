#!/usr/bin/env python3
"""Deterministically copy the selected R292 source blocks without replacements."""
from pathlib import Path
import hashlib, json

ROOT = Path(__file__).resolve().parent
REPO = ROOT.parents[1]
PROV = REPO / '.r21-scratch/r346-after-guards-raw/provenance'
FUNS = PROV / 'R292Funs.input.lean'
TYPES = PROV / 'R292Types.input.lean'
OUT = ROOT / 'AspisR357BatchZeroPredicateRaw.lean'
SOURCE_COPY = ROOT / 'source' / 'R357BatchZeroPredicateRaw.lean'

fun_bytes = FUNS.read_bytes()
type_bytes = TYPES.read_bytes()
fun_lines = fun_bytes.splitlines(keepends=True)
type_lines = type_bytes.splitlines(keepends=True)
# One-based frozen source line ranges; exact starts/ends and content are checked below.
ranges = {
    'unit_closure_type': ('types', 42, 45),
    'B_partial_eq': ('funs', 201, 209),
    'closure_call_mut': ('funs', 257, 268),
    'closure_call_once': ('funs', 270, 281),
    'closure_FnOnceInst': ('funs', 283, 293),
    'closure_FnMutInst': ('funs', 295, 307),
}
linesets = {'types': type_lines, 'funs': fun_lines}
blocks = {}
for key, (kind, first, last) in ranges.items():
    block = b''.join(linesets[kind][first - 1:last])
    blocks[key] = block
# Guard against source-range drift and accidental inclusion of a neighbor.
assert blocks['unit_closure_type'].startswith(b'/-- [aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::batch::closure]')
assert blocks['unit_closure_type'].rstrip().endswith(b'def circle_norm.joined_inverse.line_norm.r110_norm.batch.closure := Unit')
assert b'::eq]:' in blocks['B_partial_eq'].splitlines()[0]
assert b'::call_mut]:' in blocks['closure_call_mut'].splitlines()[0]
assert b'::call_once]:' in blocks['closure_call_once'].splitlines()[0]
assert b'FnOnce<' in blocks['closure_FnOnceInst'].splitlines()[0]
assert b'FnMut<' in blocks['closure_FnMutInst'].splitlines()[0]

header = b'''import Aeneas.Std
import AspisR249R110Raw
import AspisR278PrivateInverseRaw

open Aeneas Aeneas.Std Result
open AspisR249R110Raw AspisR278PrivateInverseRaw

set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

noncomputable section
namespace AspisR357BatchZeroPredicateRaw

'''
footer = b'''\n#print axioms circle_norm.joined_inverse.line_norm.r110_norm.batch.closure
#print axioms circle_norm.joined_inverse.line_norm.r110_norm.B.Insts.CoreCmpPartialEqB.eq
#print axioms circle_norm.joined_inverse.line_norm.r110_norm.batch.closure.Insts.CoreOpsFunctionFnMutTupleSharedBBool.call_mut
#print axioms circle_norm.joined_inverse.line_norm.r110_norm.batch.closure.Insts.CoreOpsFunctionFnOnceTupleSharedBBool.call_once
#print axioms circle_norm.joined_inverse.line_norm.r110_norm.batch.closure.Insts.CoreOpsFunctionFnOnceTupleSharedBBool
#print axioms circle_norm.joined_inverse.line_norm.r110_norm.batch.closure.Insts.CoreOpsFunctionFnMutTupleSharedBBool
'''
source_payload = b'\n'.join(blocks.values())
output = header + source_payload + footer
OUT.write_bytes(output)
SOURCE_COPY.write_bytes(output)

prov = ROOT / 'provenance'
(prov / 'R292Funs.input.lean').write_bytes(fun_bytes)
(prov / 'R292Types.input.lean').write_bytes(type_bytes)
for key, block in blocks.items():
    (prov / f'{key}.excerpt.lean').write_bytes(block)
report = {
  'status': 'mechanical source-fragment copy; uncompiled; not promoted',
  'source_files': {
    'R292Funs.input.lean': {'path': str(FUNS), 'sha256': hashlib.sha256(fun_bytes).hexdigest(), 'expected_sha256': '4d40a5b7b540adec90efef80a5ed8a5b4403704b388506af21f357761d95aec4'},
    'R292Types.input.lean': {'path': str(TYPES), 'sha256': hashlib.sha256(type_bytes).hexdigest(), 'expected_sha256': '972adf9e51991e13dee2e4f12621af6ba2ae613c04220bc7588ab3c8147ac833'}
  },
  'selected_source_line_ranges_1_based_inclusive': {k: {'source': kind, 'first': first, 'last': last, 'byte_sha256': hashlib.sha256(blocks[k]).hexdigest(), 'bytes': len(blocks[k])} for k,(kind,first,last) in ranges.items()},
  'exact_copy': {'replacement_count': 0, 'copied_payload_sha256': hashlib.sha256(source_payload).hexdigest(), 'copied_payload_bytes': len(source_payload), 'source_blocks_concatenated_in_order': list(blocks)},
  'output_sha256': hashlib.sha256(output).hexdigest(),
  'source_copy_sha256': hashlib.sha256(SOURCE_COPY.read_bytes()).hexdigest(),
  'source_copy_matches_output': SOURCE_COPY.read_bytes() == OUT.read_bytes(),
  'source_name_binding_inventory': {
    'batch.closure': 'local copied type alias to Unit; source Type row only',
    'B': 'existing imported AspisR249R110Raw representation; not redeclared',
    'B.ZERO': 'existing imported AspisR278PrivateInverseRaw definition',
    'B.Insts.CoreCmpPartialEqB.eq': 'local copied declaration; call_mut uses the identically qualified local name in this namespace',
    'FnOnce/FnMut': 'Aeneas Std imported trait structures; local copied trait implementation values call copied methods',
    'call_mut/call_once/FnOnceInst/FnMutInst': 'copied source declarations and implementations; no replacement or body edits'
  },
  'axioms_commands': 6,
  'validation': 'Only deterministic generator assertions and byte/hash checks were run. No Lean compile, source proof, standard-library correspondence, or whole-batch claim.'
}
(prov / 'raw-adapter.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
