#!/usr/bin/env python3
"""Validate exact evidence identities without replaying a build."""
import argparse, hashlib, json, re
from pathlib import Path
E=Path(__file__).resolve().parent.parent
ROOT=next(p for p in E.parents if (p/'Cargo.toml').exists())
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');ap.parse_args()
m=json.loads((E/'manifest.json').read_text())
for path,pin in m['sources'].items():
 p=ROOT/path
 assert sha(p)==pin['sha256'], path
 assert p.stat().st_size==pin['size_bytes'], path
for p in (E/'lean').glob('lean-*.json'):
 row=json.loads(p.read_text());a=row['attempt']
 snapshot=next((E/'lean/sources').glob('attempt-'+str(a)+'-*'))
 assert sha(snapshot)==row['source_sha256'], a
 assert hashlib.sha256(json.dumps(row['deps'],sort_keys=True).encode()).hexdigest()==row['deps_fingerprint'], a
 out=(E/'lean'/('out-'+str(a)+'.log')).read_text()
 status=int(re.search(r'^exit=(\d+)',out,re.M)[1])
 if a in m['accepted_lean_attempts']:
  assert status==0 and 'sorryAx' not in out and ': error' not in out, a
  for line in re.findall(r"'[^']+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms)",out,re.S):
   if 'depends on axioms:' in line:
    axs=set(re.search(r'\[([^\]]*)\]',line,re.S)[1].replace('\n','').replace(' ','').split(','))
    assert axs <= {'propext','Classical.choice','Quot.sound'}, (a,line)
 if a in m['excluded_lean_attempts']: assert status!=0
for p in (E/'receipts').glob('*/receipt.json'):
 row=json.loads(p.read_text());assert row['exit_status']==0, p
 assert row['swaps']==0, p
 assert row['limits']=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0','pids.max':'64'},p
for path in ['balance-m31-step-rec-v1-inputs.json','balance-qm31-step-rec-v1-inputs.json']:
 for rel,expected in json.loads((E/path).read_text())['source_hashes'].items():assert sha(ROOT/rel)==expected, rel
before=E/'headline-before.lean.txt';after=E/'headline-after.lean.txt'
assert before.read_bytes()==after.read_bytes()==(ROOT/'docs/research/v8-r0-zk-20261009/lean/R1Z/PrivacyR1HeadlineV2.lean').read_bytes()
assert (E/'headline-deletions.diff').read_bytes()==b''
for mode,row in json.loads((E/'frozen-elf-final-check.json').read_text())['programs'].items():
 assert row['byte_identical'] and row['cmp_exit']==0 and row['sha256']==row['expected_sha256'], mode
for name in ['ProverCommitBalanceRecursion','PrivacyR1HeadlineCallerScope']:
 s=(ROOT/'docs/research/v8-r0-zk-20261009/lean/R1Z'/(name+'.lean')).read_text()
 assert not re.search(r'\b(sorry|axiom|admit|native_decide)\b|set_option max(?:Heartbeats|RecDepth)',s),name
 assert len(re.findall(r'^theorem ',s,re.M))==len(re.findall(r'^#print axioms ',s,re.M)),name
if m.get('final_audit_attempt'):
 out=(E/'lean'/('out-'+str(m['final_audit_attempt'])+'.log')).read_text()
 assert out.count('depends on axioms:')+out.count('does not depend on any axioms')==m['final_audit_lines']
print(json.dumps(dict(sources=len(m['sources']),accepted_lean_attempts=len(m['accepted_lean_attempts']),excluded_lean_attempts=len(m['excluded_lean_attempts']),status='checked')))
