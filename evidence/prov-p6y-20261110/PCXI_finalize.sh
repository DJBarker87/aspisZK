#!/bin/bash
# PCXI_finalize.sh: builds PCXI_RECEIPTS.json, PCXI_SUMMARY.md, PCXI_ATTEMPTS.jsonl, PCXI_TOOLS.json from PCXI_RECEIPTS_raw.json (output of: bash PCXI_compare.sh)
cd "$(dirname "$0")"
python3 -B -I - <<'PY'
import json, collections, subprocess, hashlib
raw = json.load(open('PCXI_RECEIPTS_raw.json'))['records']
g = json.loads(subprocess.check_output(['git', 'show', 'HEAD:evidence/prov-p6v-20261110/PCXG_PROVENANCE.json']))
c = collections.Counter(r['verdict'] for r in raw)
sub = collections.Counter((r['verdict'], r.get('subtype')) for r in raw)
assert len(raw) == 183 == g['split_counts']['RECEIPTED_NO_PIN_EQUAL_EVIDENCE'] and len({(r['module'], r['definition']) for r in raw}) == 183
settled = g['SETTLED'] + c['PIN_EQUAL']; notset = g['NOT_SETTLED'] - c['PIN_EQUAL']
bymod = collections.defaultdict(collections.Counter)
for r in raw: bymod[r['module']][r['verdict']] += 1
out = dict(schema='PCXI_RECEIPTS/1', target_established=False, frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',
           scope='183 RECEIPTED cone definitions of AspisR1.TAS_FinalB.deployed_splitB without pin-equal evidence (PCXG_PROVENANCE.json split RECEIPTED_NO_PIN_EQUAL_EVIDENCE)',
           verdict_counts=dict(c), verdict_subtype_counts={'%s|%s' % k: v for k, v in sub.items()},
           split_before=dict(SETTLED=g['SETTLED'], NOT_SETTLED=g['NOT_SETTLED']), split_after=dict(SETTLED=settled, NOT_SETTLED=notset,
           NOT_SETTLED_breakdown=dict(OPEN=g['split_counts']['OPEN'], TEXT_DIFFERS=c['TEXT_DIFFERS'], NOT_REDERIVABLE=c['NOT_REDERIVABLE'])),
           other_classes_unchanged=g['OTHER_CLASSES'],
           rule='PIN_EQUAL: Rust item text (receipt source, hash-verified or in-repo) equals frozen 4bb3b3f text after whitespace/comment normalisation, local callees/types equal frozen, and either NO_ARITHMETIC or receipt overflow checks ON. TEXT_DIFFERS subtypes: TEXT, NO_FROZEN_COUNTERPART, DEPENDENCY_CONTEXT_DIFFERS, CONFIG_DIFFERS, EMISSION_DIFFERS_FROM_FRESH_FROZEN. NOT_REDERIVABLE counts OPEN.',
           by_module={m: dict(v) for m, v in sorted(bymod.items())}, records=raw)
json.dump(out, open('PCXI_RECEIPTS.json', 'w'), indent=1)
L = ['# PCXI_ summary: re-derivation of the 183 RECEIPTED cone definitions without pin-equal evidence', '',
     'Provenance only; no ledger row, trust row, RSL, contract or shipped source changed; no Lean, extraction or Kani scope was run (budget unused). Frozen source 4bb3b3f. Target not yet established.', '',
     '## Counts', '', '| verdict | definitions |', '|---|---|']
for k in ('PIN_EQUAL', 'TEXT_DIFFERS', 'NOT_REDERIVABLE'): L.append('| %s | %d |' % (k, c[k]))
L += ['', 'Subtypes: ' + '; '.join('%s/%s %d' % (k[0], k[1] or '-', v) for k, v in sorted(sub.items(), key=str)), '',
      '## Split of the 1707 cone definitions', '', '| class | before (PCXG_) | after |', '|---|---|---|',
      '| SETTLED | %d | %d |' % (g['SETTLED'], settled), '| NOT SETTLED | %d | %d |' % (g['NOT_SETTLED'], notset),
      '', 'NOT SETTLED after = OPEN %d + TEXT_DIFFERS %d + NOT_REDERIVABLE %d. Listed separately and unchanged: 65 (EQUALITY_DOMAIN 6, CONDITIONAL_ON_BINDING 43, DEPENDS_ON_LIBRARY_TRUST 7, HAND_ADAPTED 5, NO_FROZEN_COUNTERPART 4). %d + %d + 65 = 1707.' % (g['split_counts']['OPEN'], c['TEXT_DIFFERS'], c['NOT_REDERIVABLE'], settled, notset), '',
      '## What PIN_EQUAL means here', '',
      'The Rust text of the item in the receipted extraction input equals the 4bb3b3f text (normalised), its local callees and local types/consts equal their frozen counterparts, and the extraction either has no overflow-sensitive operator or ran with CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS=true. It does not prove that the gate Lean definition is that emission: the link from gate module to emitted file is the candidate sha256 of PCO_PARTITION (hash identity), unchanged. For definitions with PCO coverage COVERED_DIFFERS the Rust text can be equal while the receipted Lean differs from a fresh frozen emission; those are TEXT_DIFFERS (EMISSION_DIFFERS_FROM_FRESH_FROZEN), not credited. Dependency context of probe/cut crates was checked for local functions, types and consts only; external crate items were not compared.', '',
      '## By module', '', '| module | PIN_EQUAL | TEXT_DIFFERS | NOT_REDERIVABLE |', '|---|---|---|---|']
for m, v in sorted(bymod.items()): L.append('| %s | %d | %d | %d |' % (m, v['PIN_EQUAL'], v['TEXT_DIFFERS'], v['NOT_REDERIVABLE']))
L += ['', 'Per-definition evidence (receipt files, revision, tree-dirty flag, overflow configuration, item hashes, first difference) is in PCXI_RECEIPTS.json.', '',
      'Target not yet established.']
open('PCXI_SUMMARY.md', 'w').write('\n'.join(L) + '\n')
open('PCXI_ATTEMPTS.jsonl', 'w').write(json.dumps(dict(event='no_scopes', note='source work only; 0 Lean, 0 extraction, 0 Kani scopes launched; budget of 6 Lean scopes unused', source_revision='17700d32155', counts=dict(c))) + '\n')
tools = dict(scripts=['PCXI_compare.sh', 'PCXI_compare.py', 'PCXI_lib.py', 'PCXI_SPEC.json', 'PCXI_finalize.sh'], python='python3 -B -I', frozen='git archive/ls-tree/show of 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387 (crates/, programs/ *.rs, %d files)', inputs=['evidence/prov-p6u-20261110/PCXF_PROVENANCE.json', 'evidence/prov-p6u-20261110/PCXF_SOURCE_REVISION_AUDIT.json', 'evidence/prov-p6v-20261110/PCXG_PROVENANCE.json', 'evidence/prov-p0-20261109/PCO_PARTITION.json'],
             sha256={f: hashlib.sha256(open(f, 'rb').read()).hexdigest() for f in ['PCXI_compare.py', 'PCXI_lib.py', 'PCXI_SPEC.json']})
json.dump(tools, open('PCXI_TOOLS.json', 'w'), indent=1)
print(dict(c), settled, notset)
PY
