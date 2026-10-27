"""Validate the focused proof manifest, partition one axioms audit, replay once."""
import pathlib,json,re,hashlib,sys
R=pathlib.Path(__file__).resolve().parents[2];E=R/'evidence/pv-reach-20261027/resume7';L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
latest={}
for p in sorted(E.glob('receipt-[0-9]*.json')):
 r=json.loads(p.read_text())
 if r['accepted'] and 'PV_RE_' in r['target']:
  q=R/'docs/research/v8-r0-zk-20261009/lean'/(r['target']+'.lean')
  if q.is_file() and hashlib.sha256(q.read_bytes()).hexdigest()==r['source_sha256']:latest[r['target']]=r
assert len(latest)==17,('expected current original-prefix proof modules',len(latest))
manifest=[];allnames=set()
for label in ['A','B']:
 mods={m:r for m,r in latest.items() if (('Poison' in m or 'Excluded' in m)==(label=='B'))};names=set()
 for m,r in mods.items():
  source=R/'docs/research/v8-r0-zk-20261009/lean'/(m+'.lean');s=source.read_text()
  assert not re.search(r'\b(sorry|admit|axiom|native_decide|implemented_by)\b',s),source
  assert not re.search(r'set_option\s+(maxHeartbeats|maxRecDepth)',s),source
  for line in r['axioms']:names.add(re.match(r"'([^']+)'",line)[1])
  manifest.append(dict(module=m,attempt=r['attempt'],sha256=r['source_sha256'],path=str(source.relative_to(R))))
 text=''.join('import '+m.replace('/','.')+'\n' for m in sorted(mods))+'\n'
 text+=''.join('#print '+n+'\n#print axioms '+n+'\n' for n in sorted(names))
 dest=L/f'PV_RE_FinalAudit7{label}.lean'
 if '--check' in sys.argv:assert dest.read_text()==text
 else:dest.write_text(text)
 allnames|=names
text='''import R1Z.PV_RE_FinalAudit7A
import R1Z.PV_RE_FinalAudit7B
-- Once-only focused frozen-proof import replay; no release closure credit.
#check R1Z.PV_RE_ClientReserve7.client_to_reserve
#check R1Z.PV_RE_ClientMapError7.client_to_maperror
#check R1Z.PV_RE_ExcludedPrefixes7.excluded_poison_prefix
'''
p=L/'PV_RE_FinalAudit7C.lean'
if '--check' in sys.argv:assert p.read_text()==text
else:p.write_text(text)
out=dict(sources=sorted(manifest,key=lambda x:x['module']),audited_declarations=sorted(allnames),scope='new original-attempt/client callback prefixes and conditional failure transports',installed_dictionary_instance=False,canonical_joint_dependency_closure=False,full_execution_invocation_coverage=False,native_fixture_nonvacuity=False)
p=E/'frozen-proof-manifest.json'
if '--check' in sys.argv:assert json.loads(p.read_text())==out
else:p.write_text(json.dumps(out,indent=2)+'\n')
print('validated',len(manifest),'modules;',len(allnames),'declarations')
