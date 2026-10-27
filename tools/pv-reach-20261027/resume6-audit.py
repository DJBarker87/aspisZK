"""Freeze independent new-proof targets, partition one axioms audit, replay once."""
import pathlib,json,re,hashlib
R=pathlib.Path(__file__).resolve().parents[2];E=R/'evidence/pv-reach-20261027/resume6';L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
rows=[json.loads(p.read_text()) for p in E.glob('receipt-[0-9]*.json')];latest={}
for r in sorted(rows,key=lambda r:r['attempt']):
 if r['accepted'] and 'PV_RE_' in r['target']:
  p=R/'docs/research/v8-r0-zk-20261009/lean'/(r['target']+'.lean')
  if p.is_file() and hashlib.sha256(p.read_bytes()).hexdigest()==r['source_sha256']:latest[r['target']]=r
context={m:r for m,r in latest.items() if 'ComposedChunk' in m};boundary={m:r for m,r in latest.items() if m not in context}
allnames=set();manifest=[]
for label,mods in [('A',context),('B',boundary)]:
 names=set()
 for m,r in mods.items():
  for line in r['axioms']:names.add(re.match(r"'([^']+)'",line)[1])
 text=''.join('import '+m.replace('/','.')+'\n' for m in sorted(mods))+'\n'
 text+=''.join('#print axioms '+n+'\n' for n in sorted(names))
 if label=='B':
  for n in sorted(names):
   if n.endswith(('client_to_public','poisoned_client_failure','attempt_to_hash','client_to_hash','poisoned_hash_failure')):text+='#print '+n+'\n'
 (L/f'PV_RE_FinalAudit6{label}.lean').write_text(text);allnames|=names
 for m,r in mods.items():manifest.append(dict(module=m,attempt=r['attempt'],sha256=r['source_sha256'],path='docs/research/v8-r0-zk-20261009/lean/'+m+'.lean'))
text='import R1Z.PV_RE_FinalAudit6A\nimport R1Z.PV_RE_FinalAudit6B\n-- Once-only frozen new-proof import replay; not a release closure rebuild.\n#check R1Z.PV_RE_PublicPoison6.poisoned_client_failure\n#check R1Z.PV_RE_Op84Forward6.noCatch\n'
(L/'PV_RE_FinalAudit6C.lean').write_text(text)
(E/'frozen-proof-manifest.json').write_text(json.dumps(dict(sources=manifest,audited_declarations=sorted(allnames),scope='independent new source contexts and boundary proofs only',installed_dictionary_instance=False,canonical_joint_dependency_closure=False,full_execution_invocation_coverage=False,native_fixture_nonvacuity=False),indent=2)+'\n')
print('frozen modules',len(manifest),'audited declarations',len(allnames))
