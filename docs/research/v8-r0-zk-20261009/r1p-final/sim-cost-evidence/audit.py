"""Audit additive sources, accepted receipts, and exact headline preservation."""
import pathlib,subprocess,hashlib,json,re
E=pathlib.Path(__file__).resolve().parent; R=E.parents[1]; L=R/'lean'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
receipts=[json.loads(p.read_text()) for p in sorted(E.glob('receipt-*.json'))]
accepted=[r for r in receipts if r['exit']==0]
by_module={r['module']:r for r in accepted}
files=sorted([*L.glob('R1Z/SimCost*.lean'),L/'R1Z/PrivacyR1HeadlineV2Sim.lean'])
assert len(by_module)==len(files)
all_axioms=[]
for p in files:
 m=str(p.relative_to(L)).removesuffix('.lean');r=by_module[m];s=p.read_text()
 assert sha(p)==r['source_sha256'],m
 assert r['dependencies_stable'] and r['swaps']==0,m
 assert not re.search(r'\b(sorry|admit|native_decide)\b|^axiom\b|set_option (maxRecDepth|maxHeartbeats)',s,re.M),m
 names=re.findall(r'^theorem (\w+)',s,re.M)
 for name in names:
  assert f'#print axioms {name}' in s,(m,name)
  assert any(f'.{name}\'' in line for line in r['axioms']),(m,name)
 for line in r['axioms']:
  if 'depends on axioms:' in line:
   axioms=set(re.search(r'\[([^]]*)\]',line).group(1).replace(' ','').split(','))
   assert axioms <= {'propext','Classical.choice','Quot.sound'},line
 all_axioms.extend(r['axioms'])
old=(L/'R1Z/PrivacyR1HeadlineV2.lean').read_text()
new=(L/'R1Z/PrivacyR1HeadlineV2Sim.lean').read_text()
a=old.index('theorem privacy_headline_v2\n');b=old.index(' :\n    ZK_FSS',a);c=old.index(' := by',b)
x=new.index('theorem privacy_headline_v2_sim\n');y=new.index('\n    (C L T : Nat)',x)
assert old[a:b].replace('theorem privacy_headline_v2\n','theorem privacy_headline_v2_sim\n')==new[x:y]
assert '('+old[b+3:c].strip()+') ∧\n    ∀' in new
changes=subprocess.check_output(['git','diff','66bfd8fe5','--name-status'],text=True).splitlines()
assert all(line.startswith('A\t') for line in changes),changes
attempts=[r['attempt'] for r in receipts];assert all(9520<=a<=9599 for a in attempts)
assert len(attempts)==len(set(attempts))
keys=[(r['source_sha256'],r['deps_fingerprint']) for r in receipts];assert len(keys)==len(set(keys))
# Current remote source/object hashes, including each accepted direct import.
paths={}
base='/home/dombarker/project-offloads/aspis-joint-20261019'
for r in accepted:
 paths[f'{base}/sources/{r["module"]}.lean']=r['source_sha256']
 paths[f'{base}/objects/{r["module"]}.olean']=r['object']['sha256']
 for d in r['dependencies']:
  paths[f'{base}/sources/{d["module"]}.lean']=d['source_sha256']
  paths[f'{base}/objects/{d["module"]}.olean']=d['object_sha256']
remote=subprocess.check_output(['ssh','dombarker@100.108.41.90','sha256sum '+' '.join(sorted(paths))],text=True)
for line in remote.splitlines():
 h,p=line.split(maxsplit=1);assert h==paths[p],p
(E/'current-host-hashes.txt').write_text(remote)
result={'pass':True,'baseline':'66bfd8fe5','revision':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
 'attempts':attempts,'accepted_attempts':[r['attempt'] for r in accepted],'failed_attempts':[r['attempt'] for r in receipts if r['exit']],
 'modules':len(files),'theorem_audits':len(all_axioms),'all_standard_axioms':True,'all_zero_swap':True,
 'accepted_peak_rss_kib':max(r['peak_rss_kib'] for r in accepted),'sources':[str(p.relative_to(R)) for p in files],
 'exact_original_binders_preserved':True,'exact_original_conclusion_preserved':True,
 'new_residuals':['C L T fixed budgets/sizes','sim_preparation (Stage value/work certificate)','sim_sizes (table and reached-address bounds)'],
 'unconditional_efficiency_closure':False,'full_frozen_manifest_replayed':False,
 'remote_current_hashes_verified':len(paths)}
(E/'audit.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
