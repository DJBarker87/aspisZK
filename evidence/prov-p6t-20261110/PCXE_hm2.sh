#!/bin/bash
# PCXE_hm2.sh: PCXE_HAND_MODELS.json (deduplicated union), with classes and reach flags.
cd /Users/dominic/ZK/.worktrees/pc-prov-p6t/evidence
python3 -I -B - <<'PY'
import json, re, sys, lzma, subprocess, collections
sys.path.insert(0, 'prov-p6t-20261110')
import PCXE_lib as L
raw = json.load(open(L.SCR + '/hm_raw.json'))
pco = L.J('prov-p0-20261109/PCO_PARTITION.json')['modules']
sb_mod = L.J('prov-p6t-20261110/PCXE_SPLITB_HITS.json')['modules']
cone = lzma.open('integrate-20261111/NNH_L942/audit/NEP_proof0_AspisR1.TAS_FinalB.deployed_splitB_REACHABLE.txt.xz').read().decode().split('\n')
cone = set(x.strip() for x in cone if x.strip())
rootfile = json.load(open(L.SCR + '/rootfile.json')); roots = json.load(open(L.SCR + '/roots.json'))
closed_union = collections.defaultdict(set)   # name -> roots (filled lazily for matched names only)
# suffix index over the union of all CLOSED-root reach lists
allnames = set(); per_root = {}
for r, fl in rootfile.items():
    b = subprocess.run(['git', '-C', L.WT, 'cat-file', '-p', f'6ce07a6a593:{fl[0]}'], capture_output=True).stdout
    names = set(x.strip() for x in lzma.decompress(b).decode('utf-8', 'replace').split('\n') if x.strip())
    per_root[r] = names; allnames |= names
print('closed union names', len(allnames))
def classify(n, mod):
    if re.search(r'solana_(pubkey|hash|program_error)|(^|\.)(Pubkey|Hash|PubkeyError|ProgramError)(\.|$|\s)', n): return 'a_sdk_type_models'
    if re.search(r'chunks_exact_mut|ChunksExactMut|slice\.iter|IterMut|array\.iter|IntoIter|into_iter|Iter\.Insts', n): return 'b_core_slice_iterator_model'
    if re.search(r'^(core\.)?(option|result)\.|ok_or|map_err|from_residual|Try', n): return 'c_core_option_result_combinators'
    if re.search(r'^core\.array|^Array\.Insts|^Slice\.Insts|^core\.slice|Array\.map|array_', n): return 'd_core_array_slice_ops'
    if re.search(r'^alloc\.|Allocation|Vec\.|String\.', n): return 'e_alloc_and_allocator_models'
    if re.search(r'^core\.(num|ops|iter|cmp|clone|convert)|revFold|rangeFold|range_clone|count_ones|trailing_zeros', n): return 'f_core_num_ops_iter_models'
    if re.search(r'read_discriminant|discriminant', n): return 'g_aeneas_discriminant_helpers'
    if re.search(r'expand_values|S1Values', n): return 'h_s1_values_expand_models'
    if re.search(r'^aspis_core\.|^field\.|^fast_pairing|^atomic_statement|^pool_v1|^state_only|^r1_wire|^verifier|^transport|^circle|^trace|^BatchedWeights|^AdapterRw|^AspisR1', n): return 'i_frozen_crate_item_models_and_gate_side_adaptations'
    if re.search(r'^NNG_call|^NMP_call|H_P|import_union', n): return 'j_proof_structure_or_toolchain_adaptations'
    return 'k_other'
def crate_of(n, cls):
    if cls == 'a_sdk_type_models':
        return 'solana-pubkey 2.4.0 / solana-hash 2.3.0 / solana-program-error 2.2.2 (frozen Cargo.lock); which one depends on the name'
    if re.match(r'^(core|alloc)\.|^(Array|Slice)\.Insts|^(MutAArray)|revFold|rangeFold|range_clone', n): return 'Rust core/alloc library (not a Cargo.lock package) at the pinned nightly sysroot: nightly-2026-06-01 (PCQ*/PCUV extractions) or nightly-2026-09-17 (original NJT/NHV receipts)'
    if re.match(r'^(aspis_core|field|fast_pairing|transport|trace|state_only)', n): return 'aspis-core 0.1.0 (workspace member of frozen tree 4bb3b3f, Cargo.lock)'
    if re.match(r'^(atomic_statement|pool_v1)', n): return 'aspis-statement 0.1.0 (frozen workspace member)'
    if re.match(r'^(r1_wire|verifier|BatchedWeights)', n): return 'aspis-r1-cost-probe 0.1.0 (frozen workspace member)'
    return 'not determined by the source job'
ent = {}
for r in raw:
    if 'gate_module' not in r or not r.get('name'): continue
    k = (r['gate_module'], r['name']); e = ent.setdefault(k, dict(gate_module=r['gate_module'], name=r['name'], sources=[], gate_files=set(), gate_text=None, fresh=None, hand_evidence=[], crate_src=set(), deps=set(), has_gate=False, notes=set()))
    e['sources'].append(r['source'])
    if r.get('gate_file'): e['gate_files'].add(r['gate_file'])
    if r.get('gate_text') and not e['gate_text']: e['gate_text'] = r['gate_text']
    if r.get('fresh') and not e['fresh']: e['fresh'] = r['fresh']
    if r.get('hand') is True: e['hand_evidence'].append(r['source'] + ':hand_model_flag')
    if r.get('aeneas_generated') is False and r.get('has_gate'): e['hand_evidence'].append(r['source'] + ':gate_text_not_Aeneas_generated')
    if r.get('aeneas_generated') is True: e['hand_evidence'].append(r['source'] + ':AENEAS_GENERATED_GATE_BODY')
    if r.get('classification'): e['notes'].add(r['source'] + ':' + r['classification'])
    if r.get('crate'): e['crate_src'].add(str(r['crate'])[:300])
    if r.get('has_gate'): e['has_gate'] = True
    for d in (r.get('deps') or []) if isinstance(r.get('deps'), list) else []: e['deps'].add(str(d))
outl = []
for (m, n), e in sorted(ent.items()):
    ev = e['hand_evidence']
    if any('AENEAS_GENERATED' in x for x in ev) and not any(x.endswith('hand_model_flag') or x.endswith('not_Aeneas_generated') for x in ev): cat = 'AENEAS_GENERATED_GATE_BODY'
    elif any(x.endswith('hand_model_flag') or x.endswith('not_Aeneas_generated') for x in ev): cat = 'HAND_WRITTEN_GATE_MODEL'
    elif e['has_gate'] and e['gate_text'] and 'Source:' not in (e['gate_text'] or '')[:800]: cat = 'HAND_WRITTEN_GATE_MODEL_BY_TEXT'
    elif e['has_gate'] and e['gate_text']: cat = 'GATE_DEFINITION_FOUND_NOT_CLASSIFIED_HAND'
    else: cat = 'NO_GATE_DEFINITION_FOUND_IN_EXAMINED_FILES'
    cls = classify(n, m)
    in_cone_mod = m in sb_mod; closed_mod = m in pco and pco[m]['relied']
    suf = lambda S: [x for x in S if x == n or x.endswith('.' + n)]
    cm = suf(cone)[:3]; cl = suf(allnames)[:3]
    rts = sorted(r for r, ns in per_root.items() if any(x in ns for x in cl)) if cl else []
    rows = sorted({row for r in rts for row in roots[r]})
    outl.append(dict(gate_module=m, name=n, category=cat, class_=cls, sources=sorted(set(e['sources'])), gate_files=sorted(e['gate_files'])[:3], gate_definition_text=(e['gate_text'] or None), fresh_form=e['fresh'],
                     pinned_crate=crate_of(n, cls) if not e['crate_src'] else sorted(e['crate_src'])[0], crate_note_from_source_jobs=sorted(e['crate_src'])[:2], reached_defs_depending=sorted(e['deps'])[:12], source_job_notes=sorted(e['notes'])[:3],
                     reached_by_splitB_module=in_cone_mod, reached_by_splitB_cone_constant=bool(cm), splitB_cone_constants_matching=cm, reached_by_CLOSED_module=closed_mod, CLOSED_root_constants_matching=cl, CLOSED_roots_matching=rts[:8], n_CLOSED_roots_matching=len(rts), CLOSED_rows_via_constant=rows[:40], n_CLOSED_rows_via_constant=len(rows),
                     CLOSED_rows_via_module=(pco[m]['rows'][:40] if m in pco else []), n_CLOSED_rows_via_module=(pco[m]['n_rows'] if m in pco else 0)))
cnt = collections.Counter((x['class_'], x['category']) for x in outl)
json.dump(dict(schema='PCXE_HAND_MODELS/1', target_established=False, note='Union of every *_HAND_MODELS.json of the campaign (P1a-P1e, P2a-d, P2f, P2r, P3a, P4a, P4b, P4c, P5), deduplicated per (gate module, external name). PCQ_B and PCQE use a different layout and contribute no per-name entries here (see PCXE_CLASSIFICATIONS.json). Record only: no trust row exists or is added. Category HAND_WRITTEN_GATE_MODEL* is what could become a trust row; AENEAS_GENERATED_GATE_BODY entries are ordinary extractions of frozen functions subject to equality; NO_GATE_DEFINITION_FOUND entries are unresolved externals (open obligations, not models).',
   n_entries=len(outl), counts_by_class_and_category={f'{a} | {b}': n for (a, b), n in sorted(cnt.items())}, reach_method='module-level: gate module in the deployed_splitB cone hits / relied by a CLOSED root (PCO). constant-level: a cone/reach-list name equal to or ending with .<external name>; this over-approximates (same short name in another namespace).', entries=outl),
   open('prov-p6t-20261110/PCXE_HAND_MODELS.json', 'w'))
hw = [x for x in outl if x['category'].startswith('HAND_WRITTEN')]
print(len(outl), 'entries;', len(hw), 'hand-written;', collections.Counter(x['category'] for x in outl))
print(collections.Counter(x['class_'] for x in hw))
print('hand-written reached by splitB constant:', sum(1 for x in hw if x['reached_by_splitB_cone_constant']), 'by splitB module:', sum(1 for x in hw if x['reached_by_splitB_module']), 'by CLOSED module:', sum(1 for x in hw if x['reached_by_CLOSED_module']))
PY
