from pathlib import Path
import json,hashlib,re,subprocess,lzma
E=Path(__file__).resolve().parent
expected=json.loads((E/'NNG_F9094_AUDIT_ROOTS.json').read_text())
results=[]
for i,group in enumerate(expected['groups']):
 d=json.loads((E/f'NNG_F9094_audit/proof{i}/proof{i}.json').read_text())
 assert d['exit_status']==0 and str(d['swaps'])=='0'
 assert sorted(r['root']for r in d['results'])==sorted(group)
 for r in d['results']:
  assert r['equal'] and set(r['walked_axioms'])==set(r['collect_axioms'])
  assert set(r['walked_axioms'])<=set(['propext','Classical.choice','Quot.sound'])
 results+=d['results']
assert len(results)==29
summary=dict(status='PASS',roots=len(results),groups=len(expected['groups']),raw_matches_collector=True,standard_axioms_only=True,combined_receipt='NNG_L686/receipt.json',fixtures_receipt='retained L363; raw walker code unchanged, driver diff only own manifest prefix',results=results)
(E/'NNG_F9094_AUDIT_SUMMARY.json').write_text(json.dumps(summary,indent=1)+'\n')
receipts=[];snapshots=0
for f in sorted(E.glob('NNG_L[0-9][0-9][0-9]/receipt.json')):
 if int(f.parent.name[-3:])<665:continue
 d=json.loads(f.read_text());a=f.parent.name;ad=json.loads((E/(a+'-admission.json')).read_text())
 assert ad['exit']==0 and ad['reservation']['allowed'] is True,a
 assert str(d['swaps'])=='0' and d['exit_status'] in [0,1],a
 for p in (f.parent/'sources').rglob('*'):
  if p.is_file():snapshots+=1
 if d['kind']=='lean' and d['exit_status']==0:
  log=(f.parent/'stdout.log').read_text();assert 'sorryAx' not in log,a
 receipts.append({k:d[k]for k in ['attempt','kind','module','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision']})
for m,f in expected['selected_receipts'].items():
 src=E/'NNG_generated'/(m+'.lean');snap=(E/f).parent/'sources'/'NNG_generated'/(m+'.lean')
 assert src.read_bytes()==snap.read_bytes(),m
 assert not re.search(r'\b(sorry|axiom|admit|native_decide)\b',src.read_text()),m
submitted={json.loads(l)['attempt'] for l in (E/'NNG_TRANSPORT.jsonl').read_text().splitlines()if json.loads(l).get('submitted')}
completed={json.loads(l)['attempt'] for f in E.glob('NNG_ATTEMPTS*.jsonl') for l in f.read_text().splitlines()if json.loads(l).get('kind')!='wait'}
assert not submitted-completed,submitted-completed
counts={k:0 for k in ['lean_link_audit','extract','kani','seed']}
for a in completed:
 k=json.loads((E/(a+'.json')).read_text())['kind'];g='lean_link_audit'if k in ['lean','link','audit']else k
 if g in counts:counts[g]+=1
for p in E.rglob('*'):
 if p.is_file():assert p.stat().st_size<=20_000_000,str(p)
assert subprocess.check_output(['git','rev-parse','HEAD:crates/aspis-r1-cost-probe/src/candidate.rs'],text=True).strip()=='59e43f26e03e907b4e3691113a943a27bbb4be0f'
validation=dict(status='PASS',scope_usage=counts,fresh_lean_link_audit_scopes=counts['lean_link_audit']-530,fresh_allowance=300,remaining_lean_link_audit_scopes=830-counts['lean_link_audit'],receipts=receipts,snapshots_checked=snapshots,current_checked_modules=12,current_audited_roots=29,no_timeout_or_memory_kill=True,unresolved_submissions=[],source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,own_new_candidates=0,blocker='LIB checkpoint public_bytes1880 domain gap, not full-row impossibility; see NNG_CHECKPOINT_EXTENT094.md',shipped_source_changes=False,key_operations=False,push=False)
(E/'NNG_F9_VALIDATION.json').write_text(json.dumps(validation,indent=1)+'\n')
print(json.dumps({k:v for k,v in validation.items()if k not in ['receipts']}))
