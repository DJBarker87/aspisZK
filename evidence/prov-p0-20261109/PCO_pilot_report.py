#!/usr/bin/env python3
"""Assemble PCO_PILOT.json from the generator reports and the scope receipts (PCO_ATTEMPTS.jsonl)."""
import json
from pathlib import Path
E = Path(__file__).resolve().parent
att = {}
for l in open(E / 'PCO_ATTEMPTS.jsonl'):
    d = json.loads(l)
    if d['event'] == 'result': att[d['attempt']] = dict(target=d['module'], exit=d['exit_status'], wall_seconds=round(d['wall_seconds'], 2), peak_rss_kib=int(d['peak_rss_kib']), swaps=int(d['swaps']), source_revision=d['source_revision'], source_tree_dirty=d.get('source_tree_dirty'), print_axioms=d.get('print_axioms'))
def load(p): return json.loads((E / p).read_text())
part = load('PCO_PARTITION.json')
def cls_of(p):
    if p['status'] == 'proved': return 'rfl' if p['stage'] == 1 else 'unfold'
    return p.get('class', 'unproved')
def lane(report, M):
    out = []
    for n, p in report['per_definition'].items(): out.append(dict(definition=n, kind=p['dkind'], reached=p['reached'], result=cls_of(p), stage=p.get('stage'), detail=(p.get('error') or '')[:160] or None))
    return out
W = load('pilot/WTB_report_r2.json'); N = load('pilot/NFG_report_r2.json'); A = load('pilot/ART_report_final.json'); C = load('pilot/control_WTB_report_r1.json')
# control: all rfl by L007 log
ctl_stage = 'all 8 declarations closed by `rfl` in PCO_L007 (stage markers in PCO_L007/stdout.log.xz)'
def counts(lst):
    c = {}
    for x in lst: c[x['result']] = c.get(x['result'], 0) + 1
    return c
wl, nl, al = lane(W, 'w'), lane(N, 'n'), lane(A, 'a')
mods = {}
mods['AspisR1WideToBytesSource.Funs'] = dict(
    partition_group_prv='a_identical_to_fresh_frozen_receipted_emission', partition_group_pco=part['modules']['AspisR1WideToBytesSource.Funs']['subgroup'],
    changed_group_note='PRV classed this a_identical (all 4 reached definitions text-identical to a fresh frozen emission). The pilot shows the compiled gate module is the hand-adapted source generated-adapted/Funs.lean (3 lines replace the Aeneas iterator/zip externals by P6ToBytes.StdModel.MutableIterator, zipNext and MutableIterator.zip.trait_default); PRV had compared against the unadapted generated-original text. See PCO_CLASSIFICATIONS.json (PILOT-1).',
    extraction=['PCO_E001'], lean_final=['PCO_L008'], lean_bundle=['PCO_L005'], lean_probe=['PCO_L001', 'PCO_L002'], definitions=wl, counts=counts(wl),
    reached_counts=counts([x for x in wl if x['reached']]), fresh_dropped=W['fresh_dropped'], types_identity=W['types_identity'], externals=dict(types=W['external_types'], funs=W['external_funs']))
mods['NFG_CheckedFieldRef.Funs'] = dict(
    partition_group_prv='c2_new_extraction_and_equality', partition_group_pco=part['modules']['NFG_CheckedFieldRef.Funs']['subgroup'], changed_group_note=None,
    extraction=['PCO_E002'], lean_final=['PCO_L009'], lean_bundle=['PCO_L005'], lean_probe=['PCO_L003'], definitions=nl, counts=counts(nl), reached_counts=counts([x for x in nl if x['reached']]),
    types_identity=N['types_identity'], externals=dict(types=N['external_types'], funs=N['external_funs']),
    semantic_note='field.M31.neg: the gate (committed reference) subtracts with checked U32 arithmetic `field.P - self` (fails with integerOverflow when self > P); the frozen source emits `lift (Std.U32.wrapping_sub field.P self)`. Equal on canonical inputs self <= P, different on non-canonical U32 (the M31.add class of NML_DiffArithmetic.lean). CM31.neg and QM31.neg are text-identical but call M31.neg, so their equalities are blocked by it (PRV counted them IDENTICAL).')
tl = [dict(definition=n, kind=('type-' + t['status'].split('_')[0]), reached=t['reached'], result=({'lean_eq_proved_stage1': 'rfl', 'lean_equiv_proved_stage1': 'rfl (generated Equiv)', 'text_identical_only': 'text-identical (no Lean theorem generated)', 'external_instantiated': 'transport-needed (external type instantiated by the gate)'}.get(t['status'], t['status'])), text_identical=t['text_identical']) for n, t in A['types'].items()]
mods['AdapterRwTypes'] = dict(
    partition_group_prv='c1_extraction_exists_equality_needed', partition_group_pco=part['modules']['AdapterRwTypes']['subgroup'], changed_group_note=None,
    extraction=['PCO_E003 (spec S902, retired: only ProgramError emitted)', 'PCO_E004 (spec S903, merged owned roots)'], lean_final=['PCO_L006'], lean_probe=['PCO_L003 (parse error from `discriminant isize` metadata, fixed in the generator)'], types=tl,
    types_counts={k: sum(1 for t in A['types'].values() if t['status'].startswith(k)) for k in ('lean_eq_proved', 'lean_equiv_proved', 'text_identical_only', 'external_instantiated')},
    reached_types={n: t['status'] for n, t in A['types'].items() if t['reached']},
    external_types=A['external_types'], note='15 reached types: 10 closed by rfl (M31, SolanaDigest, 8 closure unit types), 4 structures text-identical but with nested non-simple fields (no Lean theorem generated: the Equiv generator handles parameterless structures whose fields are closed or a direct simple fresh type), 1 differing definition solana_pubkey.Pubkey: external axiom in the fresh emission, defined as Array U8 32 in the gate.')
allf = [x for x in wl + nl]
res = dict(schema=1, target_established=False, modules=mods,
           control=dict(description='Self-copy control: the gate-adapted WideToBytes Funs/Types text re-namespaced as the "fresh" emission (pilot/control_wtb). Tests the tactics, loops and the namespace/open mechanism independently of provenance; it is not evidence about extraction.', attempt='PCO_L007', declarations=8, result=ctl_stage,
                        conclusion='rfl closes loop definitions (`@[rust_loop]` through `loop (fun ..) ..`) and loop bodies at default transparency: no equation-lemma congruence strategy is needed; the loop-definition failure mode feared in the brief did not occur.'),
           calibration=dict(
               prv_estimate_rfl_overall=0.63, funs_lane_definitions=len(allf), funs_lane_reached=sum(1 for x in allf if x['reached']),
               funs_lane_rfl=sum(1 for x in allf if x['result'] == 'rfl'), funs_lane_unfold=sum(1 for x in allf if x['result'] == 'unfold'),
               funs_lane_reached_rfl=sum(1 for x in allf if x['reached'] and x['result'] == 'rfl'), funs_lane_reached_unfold=sum(1 for x in allf if x['reached'] and x['result'] == 'unfold'),
               funs_lane_reached_not_equal=sum(1 for x in allf if x['reached'] and x['result'] not in ('rfl', 'unfold')),
               types_lane_reached=15, types_lane_reached_rfl=10, types_lane_reached_text_only=4, types_lane_reached_external=1,
               caveat='n = three hand-picked modules (one a_identical, one c1, one c2); the numbers calibrate failure causes, not the 63% population rate.',
               causes_of_prv_overestimate=['PRV coverage compares one definition text at a time. A text-identical definition whose callee differs is not an equality (NFG CM31.neg/QM31.neg).',
                                           'PRV picked the committed candidate by path+imports. The compiled gate module can be another file with the same imports and namespace (WideToBytes: generated-adapted, found only by the pilot).',
                                           'Hand-written external models in the gate (FunsExternal/TypesExternal) change the types of external boundaries, so a fresh Aeneas emission does not even elaborate against them (3 impl_defs of WideToBytes).']),
           scopes=att, scope_totals=dict(extraction=sum(1 for a in att if a.startswith('PCO_E')), lean=sum(1 for a in att if a.startswith('PCO_L')), of_budget=15, extraction_cap=4, lean_cap_for_pilot=6))
Path(E / 'PCO_PILOT.json').write_text(json.dumps(res, indent=1) + '\n'); print(json.dumps(res['calibration'], indent=1)[:1800]); print(res['scope_totals'])
