#!/usr/bin/env python3
"""Final focused source/hash audit, with resource receipt; never starts Lean."""
from pathlib import Path
import hashlib,json,subprocess,time,re
E=Path(__file__).resolve().parent;R=E.parents[4]
def load(n):return json.loads((E/n).read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def git(*a):return subprocess.check_output(['git',*a],cwd=R,text=True).strip()
start=time.monotonic();cmd=['/usr/bin/time','-l','python3','-B',str(E/'impact.py'),'--check']
with (E/'validation.stdout.log').open('w') as out,(E/'validation.time.log').open('w') as err:
 p=subprocess.run(cmd,cwd=R,stdout=out,stderr=err)
wall=time.monotonic()-start
assert p.returncode==0,(p.returncode,(E/'validation.time.log').read_text())
checks={'deterministic_repins':True}
f=load('function-checks.json')['functions']
assert {(r['path'].split('/')[-1],r['function'],r['status']) for r in f if r['status']!='unchanged'}=={('fast_dots.rs','four_dots','HISTORICAL'),('fast_dots.rs','four_dots_one','new'),('fast_pairing.rs','from_limbs','HISTORICAL'),('weights.rs','powers','HISTORICAL')}
checks['exact_changed_declaration_set']=True
for method in ['new','push','finish']:
 rows=[r for r in f if r['path'].endswith('fast_pairing.rs') and r['function']==method]
 assert len(rows)==3 and all(r['status']=='unchanged' for r in rows)
 assert len({tuple(r['new_lines']) for r in rows})==3
checks['disambiguated_EbyKDot_and_EbyEDot_bodies_unchanged']=True
texts=load('extraction-text.json')['declarations'];assert len(texts)==126 and all(r['current_matches'] for r in texts)
checks['all_126_retained_extraction_text_slices_present']=True
census=load('source-census.json')['files'];assert len(census)==488 and sum(r['status']=='unchanged' for r in census)==472
checks['full_488_file_source_census']=True
expected={'fast_dots.rs':'53fa714e84ded64b844061f4d1b66ad20ee1ba48c3873a73970f80ede8a0b602','fast_pairing.rs':'2cb96261cecfd766b5e1b45a585b74c5f59c20c6be4f41e806239e2786ca7313','weights.rs':'28b558ffa9f5b004188c7f50b1597fe681186f54fb4d52a3bd125df4f2481137'}
for n,h in expected.items():assert sha(R/'crates/aspis-r1-cost-probe/src'/n)==h
checks['adopted_three_file_hashes']=True
own=load('ownership.json');assert len(own['records'])==161
assert [(r['new_owner']) for r in own['changed_declarations']]==['S4','S5','S3']
assert len({r['name'] for r in own['records']})==len(own['records'])
checks['changed_declaration_single_ownership_overlay']=True
for r in load('model-pins.json')['modules']:assert sha(R/r['path'])==r['sha256']
checks['345_model_source_hashes']=True
base=load('function-checks.json')['target_revision']
changed=git('diff','--name-only',base).splitlines()
allowed=[str(E.relative_to(R))+'/', 'docs/research/100bit-spend-path-20261013/design/CONE-AUDIT-20261021.md']
assert all(any(p.startswith(a) for a in allowed) for p in changed),changed
checks['only_authorized_evidence_and_lead_audit_changed']=True
# Explicitly preserve all non-lead rows, including the sibling S1-S6/S9 text.
report='docs/research/100bit-spend-path-20261013/design/CONE-AUDIT-20261021.md'
prior=git('show',base+':'+report).splitlines();current=(R/report).read_text().splitlines()
for s in ['S1','S2','S3','S4','S5','S6','S9']:
 before=[l for l in prior if l.startswith('| **'+s+'**')]
 after=[l for l in current if l.startswith('| **'+s+'**')]
 assert before==after
checks['session_A_rows_preserved']=True
w=subprocess.run(['git','diff','--check',base],cwd=R,capture_output=True,text=True);assert w.returncode==0,w.stdout+w.stderr
checks['whitespace']=True
metrics=(E/'validation.time.log').read_text()
def field(label):
 m=re.search(r'(?m)^\s*(\d+)\s+'+re.escape(label)+r'\s*$',metrics);return int(m.group(1)) if m else None
receipt={'schema':'lead-repin-read-only-validation-v1','target':'impact.py --check plus ownership, changed declarations and scope checks','source_revision':git('rev-parse','HEAD'),'audited_source_revision':base,'command':cmd,'exit_status':p.returncode,'wall_seconds':wall,'peak_rss_bytes':field('maximum resident set size'),'swaps':field('swaps'),'axioms':'Not run: no new or changed Lean statements; prior theorem receipts retain their original standard-axiom scope.','checks':checks,'changed_paths':changed,'input_scripts':{p.name:sha(p) for p in [E/'check.py',E/'impact.py',Path(__file__)]},'stdout_sha256':sha(E/'validation.stdout.log'),'time_log_sha256':sha(E/'validation.time.log'),'new_lean_or_release_replay':False,'target_established':False}
assert receipt['peak_rss_bytes'] is not None and receipt['swaps']==0
(E/'validation.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
print(json.dumps({'exit':0,'checks':len(checks),'wall_seconds':wall,'peak_rss_bytes':receipt['peak_rss_bytes'],'swaps':receipt['swaps']},indent=2))
