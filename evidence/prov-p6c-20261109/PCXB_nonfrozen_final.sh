#!/bin/bash
# PCXB_nonfrozen_final.sh: PCXB_NONFROZEN.json / .md = the 26 non-frozen cone modules (PCUH_NONFROZEN_STATUS.json), definition status refreshed from PCQH_ALL_STATUS.json and the deployed_splitB cone flags.
cd /Users/dominic/ZK/.worktrees/pc-prov-p6c/evidence/prov-p6c-20261109
python3 -I -B - <<'PY'
import sys, json, collections
sys.path.insert(0, '.')
import PCXB_lib as L
nf = L.J('prov-p2h-20261109/PCUH_NONFROZEN_STATUS.json'); q = L.J('prov-p1h-20261109/PCQH_ALL_STATUS.json')['modules']
mods = json.load(open(L.SCR + '/compose2_modules.json'))
def pm(label):
    if label in mods: return label
    for suf in ('_Funs', '_Types'):
        if label.endswith(suf) and label[:-len(suf)] + '.' + suf[1:] in mods: return label[:-len(suf)] + '.' + suf[1:]
out = {}; nfc = []
for m, v in nf['modules'].items():
    qd = q.get(m, {}); defs = {}
    for n, r in v['definitions'].items():
        rq = qd.get(n)
        st = rq['status'] if rq else r['status']
        defs[n] = dict(status=st, pcuh_status=r['status'], changed_since_PCUH=bool(rq and rq['status'] != r['status']), open_reason=(rq or r).get('open_reason'), theorem=(rq or r).get('theorem'), no_frozen_counterpart_reason=r.get('no_frozen_counterpart_reason'))
        if st == 'NO_FROZEN_COUNTERPART' or r.get('no_frozen_counterpart_reason'): nfc.append(dict(module=m, definition=n, reason=r.get('no_frozen_counterpart_reason') or (rq or {}).get('open_reason'), status=st))
    cnt = collections.Counter(d['status'] for d in defs.values())
    allp = set(cnt) <= {'EQUALITY_PROVED'}
    blind = 'detector_blind_note' in v and v.get('detector_blind_note')
    verdict = 'ALL_DEFINITIONS_EQUALITY_PROVED' if allp else ('UNVERIFIED' if blind else 'OPEN')
    mm = pm(m) or m
    out[m] = dict(group=v['group'], in_deployed_splitB_cone=bool(mods.get(mm, {}).get('in_splitB_cone')), in_CLOSED_root_cone=v['in_CLOSED_root_cone'], source_blob_identified=v['source_blob_identified'], source_blob_how=v.get('source_blob_how'),
                  files=[dict(gate_source_path=f['gate_source_path'], frozen_counterpart=f['frozen_counterpart'], identification=f['identification'], n_definitions_checked_by_detector=f['n_definitions_checked_by_detector']) for f in v['files']],
                  verdict=verdict, pcuh_verdict=v['verdict'], detector_blind_note=v.get('detector_blind_note'), definition_counts=dict(cnt), definitions=defs)
o = dict(schema='PCXB_NONFROZEN/1', target_established=False, frozen=nf['frozen'], n_modules=len(out), rule='PCUH rule: ALL_DEFINITIONS_EQUALITY_PROVED only if every definition of the module has an EQUALITY_PROVED record against a fresh frozen extraction on a correct basis; detector-blind modules stay UNVERIFIED; refreshed from PCQH_ALL_STATUS (P1h) statuses.',
  verdict_counts=dict(collections.Counter(v['verdict'] for v in out.values())), in_deployed_splitB_cone=sum(1 for v in out.values() if v['in_deployed_splitB_cone']),
  definition_counts=dict(collections.Counter(d['status'] for v in out.values() for d in v['definitions'].values())), changed_since_PCUH=sum(1 for v in out.values() for d in v['definitions'].values() if d['changed_since_PCUH']),
  AspisR72Sampler_older_field_rs=dict(source_file='src/field.rs', blob='a47a9996aa63c4b368a6007f4a597fdd3636c756', first_commit='0319ac2b7b5 (2026-09-28)', paths=['docs/research/v8-full-view-zk-20260912/evidence/r72-sampler/selected/source/src/field.rs', 'docs/research/v8-full-view-zk-20260912/evidence/r25-checked-dot/reduction-array/source/crates/aspis-core/src/field.rs'],
     note='M31.mul canonical fast path differs from frozen crates/aspis-core/src/field.rs:133-137 one-line body; the M31.mul/CM31.mul/CM31.square/QM31.mul equalities against the fresh frozen text were proved by P3b (full equality on all inputs, both branches), see PCXB_PROVENANCE.json record statuses'),
  gate_definitions_with_NO_FROZEN_COUNTERPART=nfc, modules=out)
json.dump(o, open('PCXB_NONFROZEN.json', 'w'), indent=1)
L_ = ['# PCXB_NONFROZEN: the 26 non-frozen cone modules', '', 'Target not yet established. Source: PCUH_NONFROZEN_STATUS.json refreshed from PCQH_ALL_STATUS.json. A module is ALL_DEFINITIONS_EQUALITY_PROVED only when every definition has an equality against a fresh frozen extraction; detector-blind modules are UNVERIFIED until then.', '',
      f"Verdicts: {o['verdict_counts']}. Definition statuses: {o['definition_counts']}. {o['in_deployed_splitB_cone']} of 26 are in the deployed_splitB cone. {len(nfc)} gate definitions have no frozen counterpart.", '', '| module | splitB | verdict | source blob | frozen counterpart(s) | definitions |', '|---|---|---|---|---|---|']
for m, v in out.items():
    L_.append(f"| {m} | {'yes' if v['in_deployed_splitB_cone'] else 'no'} | {v['verdict']} | {str(v['source_blob_identified'])[:60]} | {'; '.join(f['frozen_counterpart'].split(':')[-1] for f in v['files'])[:90]} | {v['definition_counts']} |")
L_ += ['', '## Gate definitions with NO_FROZEN_COUNTERPART', ''] + [f"* {x['module']}: `{x['definition']}` ({x['status']}): {str(x['reason'])[:160]}" for x in nfc]
L_ += ['', 'AspisR72Sampler.Funs was extracted from an older src/field.rs (blob a47a9996aa63, first commit 0319ac2b7b5); the frozen field.rs differs in M31::mul.']
open('PCXB_NONFROZEN.md', 'w').write('\n'.join(L_) + '\n')
print(o['verdict_counts'], o['definition_counts'], len(nfc), o['changed_since_PCUH'])
PY
