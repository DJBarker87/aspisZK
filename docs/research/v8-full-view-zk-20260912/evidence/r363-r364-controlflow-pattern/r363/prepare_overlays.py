#!/usr/bin/env python3
"""Generate the R363 two-file Aeneas overlay from exact pinned source fragments."""
from pathlib import Path
import hashlib, json, difflib

HERE = Path(__file__).resolve().parent
SRC = HERE.parents[1] / '.r21-scratch/r347-output-name-collision-preflight/sources'
CHARON = SRC / 'charon-ml/NameMatcher.ml'
LLBC = SRC / 'aeneas/LlbcAstUtils.ml'
CHARON_SHA = 'a6aac1d07e356b864a9146723e31401ff26be569ce2ac71d7410bc14d1bb5061'
LLBC_SHA = '5ac2c679b28df91d76b19a65d242b92916bfb3c2838b4f908a94d8bf244a8f84'
BASE_NAME_MATCHER = b'include Charon.NameMatcher\n'
BASE_NAME_MATCHER_SHA = '32c60e5ad98d4953790d2a4be557229be66951738ef8c4f8b25a170db21c4cef'

charon_bytes = CHARON.read_bytes()
llbc_bytes = LLBC.read_bytes()
assert hashlib.sha256(charon_bytes).hexdigest() == CHARON_SHA
assert hashlib.sha256(llbc_bytes).hexdigest() == LLBC_SHA
assert hashlib.sha256(BASE_NAME_MATCHER).hexdigest() == BASE_NAME_MATCHER_SHA
lines = charon_bytes.splitlines(keepends=True)
# R347 pinned Charon source, one-based inclusive source spans.
group = b''.join(lines[984:1161])       # lines 985–1161
wrappers = b''.join(lines[1161:1197])   # lines 1162–1197
assert group.startswith(b'let rec name_with_generic_args_to_pattern_aux ')
assert b'and generic_args_to_pattern ' in group
assert group.rstrip().endswith(b'    ]')
assert wrappers.startswith(b'let name_to_pattern ')
assert b'let name_with_generics_to_pattern ' in wrappers
assert wrappers.endswith(b'  pat\n')

signature_end = b'(n : T.name) (generics : generic_args option) : pattern =\n  match n with\n'
assert group.count(signature_end) == 1
guard = b'''(n : T.name) (generics : generic_args option) : pattern =
  match List.rev n, generics with
  | T.PeInstantiated binder :: reversed_prefix, (None | Some [])
    when binder.binder_params = TypesUtils.empty_generic_params ->
      let m = compute_constraints_map binder.binder_params in
      let instantiated_args =
        generic_args_to_pattern ctx c m binder.binder_value
      in
      name_with_generic_args_to_pattern_aux ctx c (List.rev reversed_prefix)
        (Some instantiated_args)
  | _ ->
  match n with
'''
patched_group = group.replace(signature_end, guard)
assert patched_group.count(b'T.PeInstantiated binder :: reversed_prefix') == 1
assert patched_group.count(b'generic_args_to_pattern ctx c m binder.binder_value') == 1

header = b'''include Charon.NameMatcher

module T = Charon.Types
module Values = Charon.Values
module TypesUtils = Charon.TypesUtils
module GAstUtils = Charon.GAstUtils

'''
name_matcher = header + patched_group + b'\n' + wrappers

name_to_pattern_call = b'Charon.NameMatcher.name_to_pattern'
name_with_generics_call = b'Charon.NameMatcher.name_with_generics_to_pattern'
assert llbc_bytes.count(name_to_pattern_call) == 2
assert llbc_bytes.count(name_with_generics_call) == 2
llbc_candidate = llbc_bytes.replace(name_to_pattern_call, b'NameMatcher.name_to_pattern').replace(
    name_with_generics_call, b'NameMatcher.name_with_generics_to_pattern')
assert llbc_candidate.count(b'NameMatcher.name_to_pattern') == 2
assert llbc_candidate.count(b'NameMatcher.name_with_generics_to_pattern') == 2

# Verify the exact LlbcAstUtils diff is exclusively the four qualified-call edits.
expected_llbc = llbc_bytes.replace(name_to_pattern_call, b'NameMatcher.name_to_pattern').replace(
    name_with_generics_call, b'NameMatcher.name_with_generics_to_pattern')
assert llbc_candidate == expected_llbc

out_name = HERE / 'source-overlay/NameMatcher.ml'
out_llbc = HERE / 'source-overlay/LlbcAstUtils.ml'
out_name.write_bytes(name_matcher)
out_llbc.write_bytes(llbc_candidate)
prov = HERE / 'provenance'
(prov / 'R347-pinned-NameMatcher.ml').write_bytes(charon_bytes)
(prov / 'R360-base-NameMatcher.ml').write_bytes(BASE_NAME_MATCHER)
(prov / 'R360-base-LlbcAstUtils.ml').write_bytes(llbc_bytes)
(prov / 'copied-pattern-generation-group.ml').write_bytes(group)
(prov / 'copied-public-pattern-wrappers.ml').write_bytes(wrappers)
(prov / 'modified-pattern-generation-group.ml').write_bytes(patched_group)
(prov / 'guard-insertion.ml').write_bytes(guard[len(b'(n : T.name) (generics : generic_args option) : pattern =\n'):])
(prov / 'LlbcAstUtils.call-routing.diff').write_text(''.join(difflib.unified_diff(
    llbc_bytes.decode().splitlines(keepends=True),
    llbc_candidate.decode().splitlines(keepends=True),
    fromfile='R360/src/llbc/LlbcAstUtils.ml', tofile='R363/src/llbc/LlbcAstUtils.ml')))
report = {
  'status': 'source overlay prepared only; no OCaml build or translation',
  'pinned_source': {
    'repository': 'ZK-v5-formal/toolchains/charon',
    'revision': 'cb50ff16b9f1066b8a97dc06da704de2da2fa41c',
    'NameMatcher_ml_sha256': hashlib.sha256(charon_bytes).hexdigest(),
    'copied_ranges_1_based_inclusive': {'mutual_pattern_generation_group': [985, 1161], 'two_public_wrappers': [1162, 1197]},
    'R347_linkage_note': 'The exact copied source file is from the pinned repository/preflight; package provenance reports a matching installed source file, but direct embedded .cmx/.o correspondence is not claimed.'
  },
  'R360_source': {
    'NameMatcher_ml_sha256': BASE_NAME_MATCHER_SHA,
    'LlbcAstUtils_ml_sha256': hashlib.sha256(llbc_bytes).hexdigest(),
    'candidate_full_ExtractTypes_sha256': '0f8ee29aa89c9456ea6c266ff8d767dcb8a83af5bbe8096d04e53582cb32c527',
    'R360_binary_sha256': '8a6cc181f75bf1c2ac64fa8c5db2bc896d5f7908b21ef94389217d9c3392c416'
  },
  'overlay': {
    'NameMatcher_ml_sha256': hashlib.sha256(name_matcher).hexdigest(),
    'LlbcAstUtils_ml_sha256': hashlib.sha256(llbc_candidate).hexdigest(),
    'original_function_group_bytes': len(group),
    'original_wrappers_bytes': len(wrappers),
    'guarded_group_sha256': hashlib.sha256(patched_group).hexdigest(),
    'guard_edits': 1,
    'guard_supported_case': 'trailing PeInstantiated binder with empty binder_params and supplied converted generics None or Some []; convert binder_value via the copied generic_args_to_pattern under compute_constraints_map binder_params, strip trailing suffix, attach converted arguments',
    'unsupported_cases': 'fall through to unchanged original copied pattern-generation body',
    'redirected_call_counts': {'name_to_pattern': 2, 'name_with_generics_to_pattern': 2},
    'LlbcAstUtils_other_byte_changes': 0,
    'logical_matching_functions_modified': False,
    'wrapper_consistency_assertions_retained_exactly': True,
    'generic_arguments_erased': False,
    'source_rows_or_attributes_modified': False
  },
  'bindings': {
    'source_overlay_implementation': 'Aeneas local NameMatcher.ml includes Charon.NameMatcher, then defines local copied generator/wrappers that shadow only pattern-generation functions.',
    'aliases': ['T=Charon.Types', 'Values=Charon.Values', 'TypesUtils=Charon.TypesUtils', 'GAstUtils=Charon.GAstUtils'],
    'helper_types_and_matchers': 'Resolved through include Charon.NameMatcher; no matcher or logical comparison function is replaced.',
    'LlbcAstUtils': 'Only the four requested wrapper calls redirect from Charon.NameMatcher to Aeneas NameMatcher; type annotations and other references stay unchanged.'
  },
  'output_hashes': {
    'NameMatcher.ml': hashlib.sha256(name_matcher).hexdigest(),
    'LlbcAstUtils.ml': hashlib.sha256(llbc_candidate).hexdigest(),
    'source_payload_sha256': hashlib.sha256(patched_group + b'\n' + wrappers).hexdigest()
  },
  'no_build_translation_or_semantic_decision': True
}
(prov / 'overlay-provenance.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
