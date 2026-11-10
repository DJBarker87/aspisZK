#!/bin/bash
# PCXB_nonfrozen3.sh: attach definition status and the recorded identification to PCXB_NONFROZEN.json; write PCXB_NONFROZEN.md summary.
cd /Users/dominic/ZK/.worktrees/pc-prov-p6c/evidence/prov-p6c-20261109
python3 -I -B - <<'PY'
import sys, json, collections
sys.path.insert(0, '.')
import PCXB_lib as L
o = json.load(open('PCXB_NONFROZEN.json')); mods = json.load(open(L.SCR + '/compose2_modules.json'))
for m, v in o['modules'].items():
    d = mods[m]['definitions']
    v['module_definition_status'] = dict(collections.Counter(r['status'] for r in d.values()))
    v['status_of_flagged_definitions'] = {}
    for f in v['files']:
        for dd in f['differing_definitions']:
            last = dd['symbol']
            hits = [n for n in d if n.split('.')[-1] == last.split('::')[-1].strip('<>')][:3]
            v['status_of_flagged_definitions'][last[:90]] = [dict(definition=n, status=d[n]['status'], reason=(d[n].get('open_reason') or '')[:120]) for n in hits]
o['identified_by_hand'] = {
  'AspisR72Sampler.Funs': dict(source_file='src/field.rs (doc comments: lines 77:4-85:5 for M31::mul)', identified_blob='a47a9996aa63c4b368a6007f4a597fdd3636c756',
     paths=['docs/research/v8-full-view-zk-20260912/evidence/r72-sampler/selected/source/src/field.rs', 'docs/research/v8-full-view-zk-20260912/evidence/r25-checked-dot/reduction-array/source/crates/aspis-core/src/field.rs'],
     first_commit_with_blob='0319ac2b7b5 (2026-09-28)', how='The doc-comment line ranges of 31 of the 32 checkable field.rs definitions of the module fall on the right identifiers in this blob (best partial match; no history blob matches all 32), and the blob text of M31::mul at lines 77-85 is `if self.0 < P && rhs.0 < P { x = (self.0 as u64)*(rhs.0 as u64); s = (x & P as u64) + (x >> 31); ... } else { reduce_u64(...) }`, which is the gate body of AspisR72Sampler.field.M31.mul (canonical fast path + reduce_u64 fallback). The sibling files r23_width.rs, r24_guarded_qm.rs, lib.rs are in evidence/r72-sampler/selected/source/src/ of the same blob set. Frozen field.rs:133-137 has the one-line body M31(reduce_u64(self.0 as u64 * rhs.0 as u64)).',
     differing_definitions='M31.mul in AspisR72Sampler.Funs; the same fast path in the V8R19 slices and FIo_NativeFuns/NFN callers and the AspisR64/65/66Field M31.mul (PCUF_FOR_P3.json lists M31.mul, CM31.mul, QM31.mul of R72Sampler and M31.mul of R64/R65/R66Field)',
     status='OPEN: FAILED/semantic in PCUF (P3 lemma not yet proved); the equality is not claimed. Mentioned as the first known case in the lead ruling.', limits='the 32nd range is unmatched, so the identification is by best match plus body text, not by whole-module range agreement')}
o['summary_counts'] = dict(modules_scanned=o['modules_scanned'], modules_flagged=o['modules_flagged'], flagged_in_splitB_cone=sum(1 for v in o['modules'].values() if v['in_splitB_cone']), flagged_in_CLOSED_cone=sum(1 for v in o['modules'].values() if v['in_CLOSED_root_cone']),
   flagged_with_unique_or_few_revision_candidates=sum(1 for v in o['modules'].values() for f in v['files'] if f['identification'] == 'UNIQUE_OR_FEW'))
json.dump(o, open('PCXB_NONFROZEN.json', 'w'), indent=1)
L_ = ['# PCXB_NONFROZEN: gate modules extracted from a source other than the frozen 4bb3b3f (detector output)', '', 'Target not yet established. Detector: Aeneas doc-comment Source line ranges against frozen file text; see detector_limits in the JSON. A flag is evidence of a different revision, not proof; an unflagged module is not shown frozen.', '',
      f"Scanned {o['modules_scanned']} in-scope emitted modules; flagged {o['modules_flagged']} ({o['summary_counts']['flagged_in_splitB_cone']} in the deployed_splitB cone).", '', '| module | group | splitB | flagged files (definitions differing; blobs matching all ranges) |', '|---|---|---|---|']
for m, v in o['modules'].items():
    L_.append(f"| {m} | {v['group']} | {'yes' if v['in_splitB_cone'] else 'no'} | " + '; '.join(f"{f['source_path'].split('/')[-1]} ({len(f['differing_definitions'])}; {f['n_blobs_matching_all_ranges']})" for f in v['files']) + ' |')
L_ += ['', 'Identified by hand: AspisR72Sampler.Funs (M31.mul canonical fast path) = blob a47a9996aa63 of src/field.rs under evidence/r72-sampler/selected/source (first commit 0319ac2b7b5, 2026-09-28). Details and limits in the JSON.']
open('PCXB_NONFROZEN.md', 'w').write('\n'.join(L_) + '\n')
print(o['summary_counts'])
PY
