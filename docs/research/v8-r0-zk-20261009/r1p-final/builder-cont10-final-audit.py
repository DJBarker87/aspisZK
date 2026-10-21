#!/usr/bin/env python3
"""Read-only final certificate audit; do not replay unchanged Lean targets."""
import hashlib,json,pathlib,re,subprocess
HERE=pathlib.Path(__file__).resolve().parent;ROOT=HERE.parents[3]
LEAN=HERE.parent/'lean'
mods=['BuilderDropFields','BuilderDropStoreComposition','BuilderForestStd','BuilderForestStdPort','BuilderForestValidatorExtracted','BuilderForestValidatorSteps','BuilderForestValidatorAcceptance','PrivacyR1FinalReleaseSource5']
sha=lambda b:hashlib.sha256(b).hexdigest()
inputs={}
for m in mods:
 p=LEAN/'R1Z'/f'{m}.lean';s=p.read_text()
 assert not re.search(r'^\s*(axiom|opaque)\s|\b(sorry|admit|native_decide)\b',s,re.M),m
 if m not in ['BuilderTreeCarryExtracted','BuilderTreeStepExtracted']:assert not re.search(r'^set_option (maxRecDepth|maxHeartbeats)',s,re.M),m
 inputs['R1Z.'+m]=dict(source_sha256=sha(p.read_bytes()),imports=re.findall(r'^import (\S+)',s,re.M),audits=re.findall(r'^#print axioms (.+)',s,re.M))
script='''import pathlib,json,hashlib
J=pathlib.Path('/home/dombarker/project-offloads/aspis-joint-20261019')
E=pathlib.Path('/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/env/J.json')
env=json.loads(E.read_text());inputs=INPUTS
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest() if p.exists() else 'missing'
pin=lambda p:dict(path=str(p),sha256=sha(p),size=p.stat().st_size) if p.exists() else None
out={}
for m,r in inputs.items():
 path=m.replace('.','/')
 deps={}
 for i in sorted(r['imports']):
  suffix=i.replace('.','/')+'.olean'
  choices=[J/'objects'/suffix]+[pathlib.Path(x)/suffix for x in env['LEAN_PATH'].split(':')]
  p=next((p for p in choices if p.exists()),None)
  assert p is not None,(m,i)
  deps[i]=pin(p)
 fp=hashlib.sha256(';'.join(i+'='+sha(J/'objects'/(i.replace('.','/')+'.olean')) for i in sorted(r['imports'])).encode()).hexdigest()[:16]
 out[m]=dict(source=pin(J/'sources'/(path+'.lean')),object=pin(J/'objects'/(path+'.olean')),deps_fingerprint=fp,imports=deps)
launcher=pathlib.Path('/home/dombarker/project-offloads/codex-cx-builder-ref10-20261021/run-joint.sh')
s=launcher.read_text()
assert 'MemorySwapMax=0' in s and 'TasksMax=64' in s
print(json.dumps(dict(modules=out,env=pin(E),lean=pin(pathlib.Path(env['LEAN'])),launcher=pin(launcher))))
'''.replace('INPUTS',repr(inputs))
remote=json.loads(subprocess.check_output(['ssh','dombarker@100.108.41.90','python3 -'],input=script,text=True))
attempts=[json.loads(x) for x in (HERE/'builder-cont10-attempts.jsonl').read_text().splitlines()]
final={};count=0
for m,r in inputs.items():
 v=remote['modules'][m]
 assert v['source']['sha256']==r['source_sha256'],m
 rec=next(x for x in reversed(attempts) if not x.get('invalid_evidence') and x['module']==m and x['exit']==0 and x['source_sha256']==r['source_sha256'] and x['deps_fingerprint']==v['deps_fingerprint'])
 assert len(rec['axioms'])==len(r['audits']),(m,r['audits'],rec['axioms'])
 for theorem in r['audits']:
  assert any(a.startswith("'"+('AspisBuilderForestValidator' if m.endswith('BuilderForestValidatorExtracted') else m)+'.'+theorem+"'") for a in rec['axioms']),(m,theorem,rec['axioms'])
 assert v['object'] is not None
 for a in rec['axioms']:
  assert 'sorryAx' not in a
  if 'depends on axioms:' in a:assert {x.strip() for x in a.split('[',1)[1].split(']',1)[0].split(',')} <= {'propext','Classical.choice','Quot.sound'}
 assert rec['swaps']=='0'
 count+=len(rec['axioms'])
 final[m]=dict(receipt={k:rec[k] for k in ['attempt','source_revision','source_dirty','source_sha256','deps_fingerprint','exit','wall','peak_rss_kib','swaps','axioms']},current=v)
unchanged=['docs/research/v8-r0-zk-20261009/lean/R1Z/PrivacyR1Final.lean','docs/research/v8-r0-zk-20261009/lean/R1Z/PrivacyR1FinalProtocol.lean','docs/research/v8-r0-zk-20261009/lean/R1Z/PrivacyR1FinalProtocolHistoryReal.lean','docs/research/v8-r0-zk-20261009/lean/R1Z/PrivacyR1FinalRelease.lean','docs/research/v8-r0-zk-20261009/lean/R1Z/BuilderRuntimeJoin.lean']
unchanged += ['docs/research/v8-r0-zk-20261009/lean/R1Z/PrivacyR1FinalReleaseSource2.lean',
 'docs/research/v8-r0-zk-20261009/lean/R1Z/PrivacyR1FinalReleaseSource.lean',
 'docs/research/v8-r0-zk-20261009/lean/R1Z/PrivacyR1FinalProtocolBuilder.lean',
 'docs/research/v8-r0-zk-20261009/lean/R1Z/PrivacyR1FinalProtocolQuotient.lean']
unchanged += ['docs/research/v8-r0-zk-20261009/lean/R1Z/PrivacyR1FinalReleaseSource3.lean']
assert not subprocess.check_output(['git','diff','e5d6d81a5','--name-only','--',*unchanged],cwd=ROOT,text=True).strip()
assert not subprocess.check_output(['git','diff','e5d6d81a5','--name-only','--','crates','programs'],cwd=ROOT,text=True).strip()
assert remote['launcher']['sha256']==sha((HERE/'builder-cont9-run-joint.sh').read_bytes())
signature=json.loads((HERE/'builder-cont10-signature-audit.json').read_text())
assert signature['deletion_only'] and not signature['added_premises'] and not signature['deleted_premises']
result=dict(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),source_dirty=bool(subprocess.check_output(['git','status','--porcelain'],cwd=ROOT,text=True).strip()),base='e5d6d81a5',module_count=len(mods),axiom_audit_count=count,modules=final,tool_environment={k:v for k,v in remote.items() if k!='modules'},unchanged_paths=unchanged,shipped_elf_rebuild_required=False,shipped_crates_and_programs_unchanged=True,frozen_elf_byte_identity='inherited pins; no changed shipped files and no redundant rebuild',full_frozen_manifest_replayed=False,signature=signature,status='Byte-level arbitrary-store frame composition, 24 proved std adapters, projected validator steps/induction/acceptance. Complete source pointer/callback/forest admission, shipped runtime inhabitant and checker/retry execution joins remain open.')
(HERE/'builder-cont10-final-audit.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS:',len(mods),'current modules,',count,'axiom audits, matching dependency fingerprints, zero swaps; original privacy roots and shipped files unchanged')
