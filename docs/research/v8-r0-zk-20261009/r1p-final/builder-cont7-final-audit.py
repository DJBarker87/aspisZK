#!/usr/bin/env python3
"""Read-only final certificate audit; do not replay unchanged Lean targets."""
import hashlib,json,pathlib,re,subprocess
HERE=pathlib.Path(__file__).resolve().parent;ROOT=HERE.parents[3]
LEAN=HERE.parent/'lean'
mods=['BuilderPartsContent','BuilderNullifierExtracted','BuilderNullifierReference','BuilderColumnsExtracted','BuilderSliceCollect','BuilderColumns','PrivacyR1FinalReleaseSource2']
sha=lambda b:hashlib.sha256(b).hexdigest()
inputs={}
for m in mods:
 p=LEAN/'R1Z'/f'{m}.lean';s=p.read_text()
 assert not re.search(r'^\s*(axiom|opaque)\s|\b(sorry|admit|native_decide)\b',s,re.M),m
 if m not in ['BuilderNullifierExtracted','BuilderColumnsExtracted']:assert not re.search(r'^set_option (maxRecDepth|maxHeartbeats)',s,re.M),m
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
launcher=pathlib.Path('/home/dombarker/project-offloads/codex-cx-builder-ref7-20261021/run-joint.sh')
s=launcher.read_text()
assert 'MemorySwapMax=0' in s and 'TasksMax=64' in s
print(json.dumps(dict(modules=out,env=pin(E),lean=pin(pathlib.Path(env['LEAN'])),launcher=pin(launcher))))
'''.replace('INPUTS',repr(inputs))
remote=json.loads(subprocess.check_output(['ssh','dombarker@100.108.41.90','python3 -'],input=script,text=True))
attempts=[json.loads(x) for x in (HERE/'builder-cont7-attempts.jsonl').read_text().splitlines()]
final={};count=0
for m,r in inputs.items():
 v=remote['modules'][m]
 assert v['source']['sha256']==r['source_sha256'],m
 rec=next(x for x in reversed(attempts) if x['module']==m and x['exit']==0 and x['source_sha256']==r['source_sha256'] and x['deps_fingerprint']==v['deps_fingerprint'])
 assert len(rec['axioms'])==len(r['audits']),(m,r['audits'],rec['axioms'])
 assert v['object'] is not None
 for a in rec['axioms']:
  assert 'sorryAx' not in a
  if 'depends on axioms:' in a:assert {x.strip() for x in a.split('[',1)[1].split(']',1)[0].split(',')} <= {'propext','Classical.choice','Quot.sound'}
 assert rec['swaps']=='0'
 count+=len(rec['axioms'])
 final[m]=dict(receipt={k:rec[k] for k in ['attempt','source_revision','source_dirty','source_sha256','deps_fingerprint','exit','wall','peak_rss_kib','swaps','axioms']},current=v)
unchanged=['docs/research/v8-r0-zk-20261009/lean/R1Z/PrivacyR1Final.lean','docs/research/v8-r0-zk-20261009/lean/R1Z/PrivacyR1FinalProtocol.lean','docs/research/v8-r0-zk-20261009/lean/R1Z/PrivacyR1FinalProtocolHistoryReal.lean','docs/research/v8-r0-zk-20261009/lean/R1Z/PrivacyR1FinalRelease.lean','docs/research/v8-r0-zk-20261009/lean/R1Z/BuilderRuntimeJoin.lean']
unchanged += ['docs/research/v8-r0-zk-20261009/lean/R1Z/PrivacyR1FinalReleaseSource.lean',
 'docs/research/v8-r0-zk-20261009/lean/R1Z/PrivacyR1FinalProtocolBuilder.lean',
 'docs/research/v8-r0-zk-20261009/lean/R1Z/PrivacyR1FinalProtocolQuotient.lean']
assert not subprocess.check_output(['git','diff','b7a4cc502','--name-only','--',*unchanged],cwd=ROOT,text=True).strip()
assert subprocess.check_output(['git','diff','b7a4cc502','--name-only','--','crates','programs'],cwd=ROOT,text=True).splitlines()==['crates/aspis-statement/src/spend.rs']
old=subprocess.check_output(['git','show','b7a4cc502:crates/aspis-statement/src/spend.rs'],cwd=ROOT)
assert (ROOT/'crates/aspis-statement/src/spend.rs').read_bytes().startswith(old)
assert remote['launcher']['sha256']==sha((HERE/'builder-cont7-run-joint.sh').read_bytes())
host=json.loads((HERE/'builder-cont7-host-evidence.json').read_text())
assert set(host['frozen_elf_matches'])=={'default','devnet','pool'}
assert all(x['exit']==0 and x['current']==x['frozen'] for x in host['elf_cmp'].values())
assert not {n:v for n,v in host['checkout_comparison']['stage0/src']['mismatches'].items() if n.startswith(('crates/','programs/'))}
result=dict(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),base='b7a4cc502',module_count=len(mods),axiom_audit_count=count,modules=final,tool_environment={k:v for k,v in remote.items() if k!='modules'},unchanged_paths=unchanged,shipped_elf_rebuild_required=True,frozen_elf_byte_identity_passed=True,full_frozen_manifest_replayed=False,status='Partial closure: owned nullifier callback and conditional canonical Parts handoff; source admission and concrete runtime/execution joins remain open.')
(HERE/'builder-cont7-final-audit.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS:',len(mods),'current modules,',count,'axiom audits, unchanged dependency fingerprints, zero swaps; original privacy roots unchanged; three frozen ELFs byte-identical')
