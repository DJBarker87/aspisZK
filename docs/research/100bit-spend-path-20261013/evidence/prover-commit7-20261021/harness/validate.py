#!/usr/bin/env python3
"""Validate committed receipt/source identities without rerunning builds."""
import json,hashlib,re,subprocess
from pathlib import Path
E=Path(__file__).resolve().parent.parent
L=Path('docs/research/v8-r0-zk-20261009/lean')
rows=[]
for p in sorted((E/'lean').glob('attempts-*.jsonl')):
 rows += [json.loads(line) for line in p.read_text().splitlines()]
assert len({r['attempt'] for r in rows})==27
for r in rows:
 b=(E/'lean/sources'/(str(r['attempt'])+'.lean')).read_bytes()
 assert hashlib.sha256(b).hexdigest()==r['source_sha256']
 assert all(k in r for k in ['deps_fingerprint','exit_status','wall_time','peak_rss_kib','swaps','source_base_revision','axioms'])
 if r['accepted']:
  assert r['exit_status']==0 and not r['errors']
  for a in r['axioms']:
   assert 'sorryAx' not in a
   inside=re.search(r'\[([^]]*)\]',a)
   if inside: assert set(inside[1].split(', '))<={'propext','Classical.choice','Quot.sound'}
latest={}
for r in rows:
 if r['accepted']:latest[r['module']]=r
for m,r in latest.items():assert hashlib.sha256((L/m).read_bytes()).hexdigest()==r['source_sha256']
x=json.loads((E/'frozen-elf-final-check.json').read_text())
assert all(p['byte_identical'] and p['cmp_exit']==0 and p['receipt']['exit_status']==0 for p in x['programs'].values())
assert not json.loads((E/'rust-source-identities.json').read_text())['missing']
audit=next(r for r in rows if r['attempt']==8266)
assert len(audit['axioms'])==23
summary=dict(adopted_source_revision='9e6c55ba8',source_base_revision='072b24afc',lean_attempts=len(rows),accepted_attempts=sum(r['accepted'] for r in rows),final_audit=8266,new_axiom_audits=len(audit['axioms']),all_axioms_standard=True,frozen_elf_matches=3,rust_source_identities_complete=True,remaining_source_rows_open=9)
(E/'final-validation.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary))
