"""Read-only retained-input/extraction audit; no build or Lean replay."""
import collections
import copy
import difflib
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys

p = Path(sys.argv[1])
sha = lambda b: hashlib.sha256(b).hexdigest()
fh = lambda f: sha(f.read_bytes())
load = lambda r: json.loads((p / r).read_text())
meta = load('candidate-source-manifest.json')
base = load('input/merged-source-manifest.json')
assert fh(p/'input/merged-source-manifest.json') == meta['base_manifest_sha256']
rows = {r['merged_path']: r for r in meta['source_files']}
assert len(rows) == len(base['source_files']) == 133
changes = []
for row in base['source_files']:
    rel = row['merged_path']
    digest = fh(p/'input'/rel)
    assert digest == rows[rel]['candidate_sha256']
    if digest != row['sha256']:
        changes.append(rel)
assert set(changes) == {'src/statement/state_only_poseidon.rs',
                        'src/statement/pool_v1/pair_forest_semantic_terminal.rs'}
patch = []
for row in meta['candidate_changes']:
    rel = row['path']
    old, new = p/'provenance/F-base'/rel, p/'input'/rel
    assert fh(old) == row['base_sha256'] and fh(new) == row['candidate_sha256']
    patch.extend(difflib.unified_diff(old.read_text().splitlines(keepends=True), new.read_text().splitlines(keepends=True), fromfile='a/'+rel, tofile='b/'+rel))
assert ''.join(patch) == (p/'actual-merged-input.patch').read_text()
calls = sum((p/'input'/r).read_text().count('crate::array_from_fn_copy::<_, ') for r in changes)
assert calls == 18
assert fh(p/'input/Cargo.lock') == 'e1ff38c257fe01c028da4dfecba548f9276ceb587d35e33decafa4b72f5dd359'

stages = []
for stage in ['build', 'charon', 'aeneas']:
    r = load('receipts/'+stage+'.json')
    launch = load('scope-launches/'+stage+'.json')
    reservation = load('reservations/'+stage+'.json')
    log = (p/'logs'/f'{stage}.log').read_text()
    assert r['exit_status'] == launch['exit_status'] == 0
    assert r['candidate_manifest_sha256'] == fh(p/'candidate-source-manifest.json')
    assert r['runner_sha256'] == fh(p/'run_attempt.py')
    assert int(re.search(r'Maximum resident set size \(kbytes\): (\d+)', log).group(1)) == r['peak_process_rss_kib']
    assert int(re.search(r'\bSwaps: (\d+)', log).group(1)) == 0
    assert int(re.search(r'Exit status: (\d+)', log).group(1)) == 0
    assert re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (\S+)', log).group(1) == r['usr_bin_time_wall']
    assert int(r['cgroup_memory_high']) == 4*2**30 and int(r['cgroup_memory_max']) == 6*2**30
    assert int(r['cgroup_memory_swap_max']) == int(r['cgroup_memory_swap_peak_bytes']) == 0
    assert int(r['cgroup_pids_max']) == 128
    assert reservation['projected_total_bytes'] <= reservation['policy_limit_bytes']
    assert reservation['shared_target_active_writers'] == []
    assert json.loads(launch['stdout']) == r
    if stage == 'build':
        assert all(a in r['command'] for a in ['--release', '--locked', '--offline'])
    stages.append(r)

original = load('Terminal.llbc')
adapted = load('Terminal-name-adapt.llbc')
rename = load('name-adapter.json')
assert fh(p/'Terminal.llbc') == rename['original_sha256']
assert fh(p/'Terminal-name-adapt.llbc') == rename['adapted_sha256']
assert not original['has_errors'] and not adapted['has_errors']
fid = rename['function_id']
f = adapted['translated']['fun_decls'][fid]
assert [x['Ident'][0] for x in f['item_meta']['name']] == ['aspis_r1_mask_extraction_probe', 'field', 'M31']
assert f['item_meta']['span']['data']['beg']['line'] == 23
assert f['item_meta']['attr_info']['rename'] == 'M31_constructor'
reversed_adaptation = copy.deepcopy(adapted)
reversed_adaptation['translated']['fun_decls'][fid]['item_meta']['attr_info']['rename'] = None
assert reversed_adaptation == original
embedded_sources = []
for f in original['translated']['files']:
    if f and f['crate_name'] == 'aspis_r1_mask_extraction_probe' and 'Local' in f['name']:
        rel = f['name']['Local']
        assert (p/'input'/rel).read_text() == f['contents'], rel
        embedded_sources.append({'path': rel, 'sha256': sha(f['contents'].encode())})
categories = collections.Counter()
functions = [f for f in adapted['translated']['fun_decls'] if f]
for f in functions:
    body = f['body']
    kind = next(iter(body)) if isinstance(body, dict) else body
    categories[(f['item_meta']['is_local'], f['item_meta']['opacity'], kind)] += 1
assert len(adapted['translated']['fun_decls']) == 531 and len(functions) == 336
assert categories[(True, 'Transparent', 'Structured')] == 242
assert categories[(False, 'Foreign', 'Opaque')] == 90
targets = []
for f in functions:
    names = [n['Ident'][0] for n in f['item_meta']['name'] if 'Ident' in n]
    if names[-1] in ['terminal_qm31_probe', 'terminal_qm31', 'terminal_parts', 'composition_parts']:
        assert f['item_meta']['is_local'] and f['item_meta']['opacity'] == 'Transparent' and 'Structured' in f['body']
        targets.append({'name_components': names, 'source_sha256': sha(f['item_meta']['source_text'].encode())})
assert len(targets) == 4

# Comparison deliberately counts docblocks, not Rust functions; some blocks
# contain trait dictionaries. Source line-number changes are excluded.
spec = importlib.util.spec_from_file_location('block_compare', p/'compare-generated-blocks.py')
mod = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)
old, new = p/'provenance/G-generated', p/'output/generated/AspisR1SelectedMaskProbe'
comparison = {n: mod.compare(mod.blocks(old/n), mod.blocks(new/n)) for n in ['Funs.lean', 'Types.lean']}
f = comparison['Funs.lean']; t = comparison['Types.lean']
assert (f['exact_shared_bodies'], f['changed_paired_bodies'], f['new_only_declarations'], f['old_only_declarations']) == (204, 34, 2, 0)
assert t['exact_shared_bodies'] == t['old_blocks'] == t['new_blocks'] == 58
old_axioms, new_axioms = map(set, [mod.axioms(old/'FunsExternal_Template.lean'), mod.axioms(new/'FunsExternal_Template.lean')])
assert len(old_axioms) == 20 and len(new_axioms) == 17 and not (new_axioms - old_axioms)
assert len(old_axioms - new_axioms) == 3
assert 'core.array.from_fn' in old_axioms - new_axioms
output_hashes = {f.name: fh(f) for f in sorted(new.glob('*.lean'))}
assert output_hashes == load('output/output-audit.json')['generated_file_hashes']
translation = load('output/generated/translation.json')
counts = {k: len(translation[k]) for k in ['functions', 'types', 'trait_impls']}
assert counts == {'functions': 220, 'types': 59, 'trait_impls': 60}
print(json.dumps({'schema': 'aspis-copy-indexed-extraction-root-audit.v1',
    'scope': 'Retained source/receipt/LLBC/generated-text audit only; no compiler-preservation, old/new semantic equivalence, production adoption, full Lean proof or CU claim.',
    'base_revision': meta['base_source_revision'], 'source_rows_checked': 133,
    'changed_source_rows': changes, 'root_and_source_changes': meta['candidate_changes'],
    'actual_input_patch_sha256': fh(p/'actual-merged-input.patch'),
    'preliminary_patch_limitation': 'candidate.patch targets earlier source-kit framing. actual-merged-input.patch is the exact retained merged-input diff.',
    'stage_receipts_checked': stages, 'metadata_only_name_adapter': rename,
    'embedded_source_files_checked': embedded_sources, 'target_functions': targets,
    'llbc_categories': [{'is_local': a, 'opacity': b, 'body_kind': c, 'count': n} for (a,b,c),n in sorted(categories.items())],
    'legacy_output_audit_label_correction': 'The legacy inventory prints O for string Opaque by indexing the first character; this review records the full Opaque tag.',
    'translation_metadata_counts': counts, 'external_templates_removed': sorted(old_axioms-new_axioms),
    'external_templates_remaining': sorted(new_axioms), 'generated_file_hashes': output_hashes,
    'generated_docblock_comparison': comparison}, indent=2))
