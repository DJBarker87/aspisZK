#!/usr/bin/env python3
"""Validate retained receipts and pins without rerunning a build or proof."""
import ast,hashlib,json,re
from pathlib import Path
E=Path(__file__).resolve().parent.parent
R=next(p for p in E.parents if (p/'Cargo.toml').exists())
for p in (E/'harness').glob('*.py'):ast.parse(p.read_text(),filename=str(p))
release=json.loads((E/'source-release.json').read_text())
for rel,sha in release['files'].items():assert hashlib.sha256((R/rel).read_bytes()).hexdigest()==sha,rel
rows=[json.loads(s) for s in (E/'lean/attempts.jsonl').read_text().splitlines()]
assert rows[-1]['attempt']==8157 and rows[-1]['accepted']
allowed={'propext','Classical.choice','Quot.sound'}
for x in rows:
 if not x['accepted']:continue
 for line in x['axioms']:
  assert 'sorryAx' not in line
  names=re.search(r'axioms: \[(.*)\]',line)
  assert names and set(s.strip() for s in names[1].split(',') if s.strip())<=allowed,line
assert len(rows[-1]['axioms'])==15
elf=json.loads((E/'frozen-elf-final-check.json').read_text())
assert set(elf['programs'])=={'default','devnet','pool'}
for x in elf['programs'].values():assert x['byte_identical'] and x['sha256']==x['expected_sha256'] and x['cmp_exit']==0
check=json.loads((E/'checklist-before-after.json').read_text())
p=R/'docs/research/v8-r0-zk-20261009/r1p-final/PRIVACY-FINAL-20261020.md'
assert hashlib.sha256(p.read_bytes()).hexdigest()==check['checklist_sha256']
assert len(check['rows'])==9 and all(not x['discharged'] and x['before_verbatim']==x['after_verbatim'] for x in check['rows'])
assert json.loads((E/'reference-llbc.json').read_text())['has_errors'] is False
receipts=[]
for p in sorted((E/'receipts').glob('*/receipt.json')):
 x=json.loads(p.read_text());lim=x['limits']
 assert lim==dict(zip(['memory.high','memory.max','memory.swap.max','pids.max'],['6442450944','8589934592','0','64'])),p
 if 'kani' in x['command'] and x['exit_status']==0:assert '--unwinding-assertions' in x['command'],p
 receipts.append(dict(name=p.parent.name,exit_status=x['exit_status'],wall_seconds=x['wall_seconds'],reported_peak_rss_kib=x['peak_rss_kib'],swaps=x['swaps'],cgroup_memory_peak_bytes=x['cgroup_memory_peak_bytes']))
(E/'receipt-index.json').write_text(json.dumps(receipts,indent=2)+'\n')
print(json.dumps(dict(validated=True,lean_attempts=len(rows),final_audit_lines=15,checklist_rows_discharged=0,frozen_elf_matches=3,receipts=len(receipts))))
