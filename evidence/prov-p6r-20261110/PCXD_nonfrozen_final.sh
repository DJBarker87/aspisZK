#!/bin/bash
# PCXD_nonfrozen_final.sh: PCXD_NONFROZEN.json / .md = the 26 non-frozen cone modules (PCUH_NONFROZEN_STATUS.json), definition status refreshed from PCQH_ALL_STATUS.json and the deployed_splitB cone flags.
cd /Users/dominic/ZK/.worktrees/pc-prov-p6r/evidence/prov-p6r-20261110
python3 -I -B - <<'PY'
import sys, json, collections
sys.path.insert(0, '.')
import PCXD_lib as L
nf = L.J('prov-p2h-20261109/PCUH_NONFROZEN_STATUS.json'); q = L.J('prov-p2j-20261110/PCUJ_ALL_STATUS.json')['modules']
mods = json.load(open(L.SCR + '/compose2_modules.json'))
def pm(label):
    if label in mods: return label
    for suf in ('_Funs', '_Types'):
        if label.endswith(suf) and label[:-len(suf)] + '.' + suf[1:] in mods: return label[:-len(suf)] + '.' + suf[1:]
reach = {x['definition']: x for x in json.load(open('../prov-p6x-20261110/PCXC_NOFROZEN_REACH.json'))['definitions']}
out = {}; nfc = []
for m, v in nf['modules'].items():
    qd = q.get(m, {}); defs = {}
    for n, r in v['definitions'].items():
        rq = qd.get(n)
        st = rq['status'] if rq else r['status']
        defs[n] = dict(status=st, pcuh_status=r['status'], changed_since_PCUH=bool(rq and rq['status'] != r['status']), open_reason=(rq or r).get('open_reason'), theorem=(rq or r).get('theorem'), no_frozen_counterpart_reason=r.get('no_frozen_counterpart_reason'))
        if st == 'NO_FROZEN_COUNTERPART' or r.get('no_frozen_counterpart_reason'):
            rc = reach.get(n)
            nfc.append(dict(module=m, definition=n, reason=r.get('no_frozen_counterpart_reason') or (rq or {}).get('open_reason'), status=st,
                            reach=(dict(reachable_from_deployed_splitB=rc['reachable_from_deployed_splitB'], reachable_from_a_CLOSED_row_root=rc['reachable_from_a_CLOSED_row_root'], n_closed_roots=rc['n_roots_reaching'], splitB_witness_hops=rc['splitB_witness']['hops'], source='PCXC_NOFROZEN_REACH.json (PCXC_L006/L007; constant-level, not semantic use)') if rc else None)))
    cnt = collections.Counter(d['status'] for d in defs.values())
    allp = set(cnt) <= {'EQUALITY_PROVED'}
    blind = 'detector_blind_note' in v and v.get('detector_blind_note')
    verdict = 'ALL_DEFINITIONS_EQUALITY_PROVED' if allp else ('UNVERIFIED' if blind else 'OPEN')
    mm = pm(m) or m
    out[m] = dict(group=v['group'], in_deployed_splitB_cone=bool(mods.get(mm, {}).get('in_splitB_cone')), in_CLOSED_root_cone=v['in_CLOSED_root_cone'], source_blob_identified=v['source_blob_identified'], source_blob_how=v.get('source_blob_how'),
                  files=[dict(gate_source_path=f['gate_source_path'], frozen_counterpart=f['frozen_counterpart'], identification=f['identification'], n_definitions_checked_by_detector=f['n_definitions_checked_by_detector']) for f in v['files']],
                  verdict=verdict, pcuh_verdict=v['verdict'], detector_blind_note=v.get('detector_blind_note'), definition_counts=dict(cnt), definitions=defs)
o = dict(schema='PCXD_NONFROZEN/1', target_established=False, frozen=nf['frozen'], n_modules=len(out), rule='PCUH rule: ALL_DEFINITIONS_EQUALITY_PROVED only if every definition of the module has an EQUALITY_PROVED record against a fresh frozen extraction on a correct basis; detector-blind modules stay UNVERIFIED; refreshed from PCUJ_ALL_STATUS (P2j; PCQH vocabulary) statuses plus the PCXD overlays.',
  verdict_counts=dict(collections.Counter(v['verdict'] for v in out.values())), in_deployed_splitB_cone=sum(1 for v in out.values() if v['in_deployed_splitB_cone']),
  definition_counts=dict(collections.Counter(d['status'] for v in out.values() for d in v['definitions'].values())), changed_since_PCUH=sum(1 for v in out.values() for d in v['definitions'].values() if d['changed_since_PCUH']),
  AspisR72Sampler_older_field_rs=dict(source_file='src/field.rs', blob='a47a9996aa63c4b368a6007f4a597fdd3636c756', first_commit='0319ac2b7b5 (2026-09-28)', paths=['docs/research/v8-full-view-zk-20260912/evidence/r72-sampler/selected/source/src/field.rs', 'docs/research/v8-full-view-zk-20260912/evidence/r25-checked-dot/reduction-array/source/crates/aspis-core/src/field.rs'],
     note='M31.mul canonical fast path differs from frozen crates/aspis-core/src/field.rs:133-137 one-line body; the M31.mul/CM31.mul/CM31.square/QM31.mul equalities against the fresh frozen text were proved by P3b (full equality on all inputs, both branches), see PCXD_PROVENANCE.json record statuses'),
  gate_definitions_with_NO_FROZEN_COUNTERPART=nfc,
  no_frozen_counterpart_reach_summary=dict(definitions=len(reach), reachable_from_deployed_splitB=sum(1 for x in reach.values() if x['reachable_from_deployed_splitB']), reachable_from_a_CLOSED_row_root=sum(1 for x in reach.values() if x['reachable_from_a_CLOSED_row_root']), unreachable=sum(1 for x in reach.values() if not x['reachable_from_deployed_splitB'] and not x['reachable_from_a_CLOSED_row_root']),
     note='PCXC_ result carried unchanged: all 8 are reachable at constant level from the headline and from closed-row roots; constant-level reachability is not semantic use and says nothing about whether the Rust function runs in the ELF.'),
  NJT_claims_ref_note='NJT_ClaimsRef.r1_semantic.NJT_claims_ref is a hash-linked reference, not an orphan: the reference function (sha256 2bf403f75b4f9fb0d834bec61771d156c5555bd4fdf3dcdd804840ca58a6e5ea, NJT_REFERENCE_PINS) is appended to the frozen r1_semantic.rs (sha256 c66eba53bc3cdf801466455089d7189c02a0bec858f407a5fc9db35d10b17013) giving the scratch tree file e2a6d18185b13d5d6d7858284e30310119d53bac7e48d15c210152f847c553ea; PCWC_E002 re-extracted it byte-identically to the recorded outputs (PCWC_NJT.json). It has no counterpart in the frozen source proper because it is the reference of the claims candidate, linked to the frozen text by those hashes; it serves 12 CLOSED rows.',
  modules=out)
json.dump(o, open('PCXD_NONFROZEN.json', 'w'), indent=1)
L_ = ['# PCXD_NONFROZEN: the 26 non-frozen cone modules', '', 'Target not yet established. Source: PCUH_NONFROZEN_STATUS.json refreshed from PCUJ_ALL_STATUS.json. A module is ALL_DEFINITIONS_EQUALITY_PROVED only when every definition has an equality against a fresh frozen extraction; detector-blind modules are UNVERIFIED until then.', '',
      f"Verdicts: {o['verdict_counts']}. Definition statuses: {o['definition_counts']}. {o['in_deployed_splitB_cone']} of 26 are in the deployed_splitB cone. {len(nfc)} gate definitions have no frozen counterpart.", '', '| module | splitB | verdict | source blob | frozen counterpart(s) | definitions |', '|---|---|---|---|---|---|']
for m, v in out.items():
    L_.append(f"| {m} | {'yes' if v['in_deployed_splitB_cone'] else 'no'} | {v['verdict']} | {str(v['source_blob_identified'])[:60]} | {'; '.join(f['frozen_counterpart'].split(':')[-1] for f in v['files'])[:90]} | {v['definition_counts']} |")
L_ += ['', '## Gate definitions with NO_FROZEN_COUNTERPART', ''] + [f"* {x['module']}: `{x['definition']}` ({x['status']}): {str(x['reason'])[:160]}" for x in nfc]
L_ += ['', '## Reach of the 8 gate-only definitions (PCXC_NOFROZEN_REACH.json)', '', 'All 8 are reachable at constant level from AspisR1.TAS_FinalB.deployed_splitB and from at least one CLOSED-row root; none is unreachable. This is not semantic use.', '']
L_ += [f"* `{x['definition']}`: splitB {x['reach']['reachable_from_deployed_splitB']}, {x['reach']['n_closed_roots']} closed-row roots, shortest witness {x['reach']['splitB_witness_hops']} hops" for x in nfc if x.get('reach')]
L_ += ['', '## NJT_claims_ref', '', o['NJT_claims_ref_note']]
L_ += ['', 'AspisR72Sampler.Funs was extracted from an older src/field.rs (blob a47a9996aa63, first commit 0319ac2b7b5); the frozen field.rs differs in M31::mul.']
open('PCXD_NONFROZEN.md', 'w').write('\n'.join(L_) + '\n')
print(len([x for x in nfc if x.get('reach')]), o['verdict_counts'], o['definition_counts'], len(nfc), o['changed_since_PCUH'])
PY
