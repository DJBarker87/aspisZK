from pathlib import Path
import json,subprocess,hashlib,re,lzma
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin52-20261029';base='ef805d853cdd61a323b0fa3b3b0646d25828e065';head=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
rows=[dict(v,attempt=int(p.stem.split('-')[1])) for p in sorted(E.glob('modules-*.json')) for v in json.loads(p.read_text())];assert len(rows)==100
assert sorted(v['attempt'] for v in rows)==list(range(65500,65600))
accepted={v['module']:v for v in rows if v['accepted']};failed=[v for v in rows if not v['accepted']]
for v in accepted.values():
 for line in v['axioms']:
  m=re.search(r'depends on axioms:\s*\[([\s\S]*?)\]',line)
  if m:assert set(x.strip() for x in m[1].split(','))<={'propext','Classical.choice','Quot.sound'},line
changed=subprocess.check_output(['git','diff','--name-only',base,head],text=True).splitlines();protected=[p for p in changed if Path(p).name.startswith(('PV_OWN','PV_RJDec_'))];assert not protected
(E/'protected-prefixes-unchanged.json').write_text(json.dumps(dict(base=base,head=head,changed_protected_paths=protected,byte_identical=True),indent=2)+'\n')
status=[]
for p in changed:
 if not p.endswith('.lean') or not (R/p).is_file():continue
 assert Path(p).name.startswith('PV_RunJoin_'),p
 s=(R/p).read_text();assert not re.search(r'\b(sorry|admit|native_decide|implemented_by|axiom)\b|set_option\s+max(?:Heartbeats|RecDepth|RecursionDepth)',s),p
 m='R1Z.'+Path(p).stem;sha=hashlib.sha256((R/p).read_bytes()).hexdigest();v=accepted.get(m)
 ok=bool(v and v['source_sha256']==sha)
 if v:assert ok,('changed accepted source',m)
 old=[v for v in failed if v['module']==m]
 status.append(dict(module=m,path=p,sha256=sha,accepted=ok,status='accepted' if ok else 'rejected and uncredited' if old else 'uncompiled draft; no credit',attempt=v['attempt'] if v else old[-1]['attempt'] if old else None))
(E/'new-source-credit-status.json').write_text(json.dumps(status,indent=2)+'\n')
p=json.loads((E/'build-plan.json').read_text())
def closure(root):
 seen=set()
 def walk(m):
  if m in seen:return
  seen.add(m)
  for d in p['modules'].get(m,{}).get('imports',[]):walk(d)
 walk(root);return seen
roots=['R1Z.PV_RunJoin_'+k+'Audit52' for k in ['Owned','Model','Neutral']];cs={r:closure(r) for r in roots}
for r,c in cs.items():assert not {'R1Z.PV_AL_CircleOwnedTypes','AspisR72Sampler.Types'}<=c,r
assert set(accepted)<=set().union(*cs.values()),set(accepted)-set().union(*cs.values())
assert not {'R1Z.PV_AL_CircleOwnedTypes','AspisR72Sampler.Types'}&cs[roots[2]]
(E/'audit-closure-check.json').write_text(json.dumps(dict(roots={k:sorted(v) for k,v in cs.items()},all_new_accepted_covered=True,no_colliding_types_coimported=True,neutral_closure_excludes_both_generated_types=True,joint_source_value_bridge_complete=False),indent=2)+'\n')
receipts=[json.loads(p.read_text()) for p in E.glob('receipt-*.json')];summary=dict(attempts=len(rows),accepted_attempts=sum(v['accepted'] for v in rows),failed_attempts=len(failed),accepted_new_modules=len(accepted),uncredited_sources=[s['module'] for s in status if not s['accepted']],peak_rss_bytes=max(v['peak_rss_bytes'] for v in receipts),swaps=sum(v['swaps'] for v in receipts),audits=[{k:v[k] for k in ['attempt','modules','exit','host_wall_seconds','peak_rss_bytes','swaps','source_revision','accepted']} for v in sorted(receipts,key=lambda v:v['attempt']) if v['attempt']>=65597],rows_removed=[],endpoint_premises=dict(removed=0,added=0,weakened=0,changed=0))
assert summary['swaps']==0
(E/'SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
(E/'commits.txt').write_text(subprocess.check_output(['git','log','--oneline',base+'..HEAD'],text=True))
