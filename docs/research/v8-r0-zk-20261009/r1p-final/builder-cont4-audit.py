#!/usr/bin/env python3
"""Focused continuation-4 source/receipt audit; never reruns a proof."""
import hashlib,json,pathlib,re,subprocess
HERE=pathlib.Path(__file__).resolve().parent
ROOT=HERE.parents[3]
E=HERE/'builder-cont4-evidence'
mods=['BuilderProtocolInstance','BuilderRecordCanonical','BuilderPublicCanonical',
 'BuilderRuntimeJoin','BuilderExtractedRecords','BuilderProtocolBounds','BuilderFieldNormalization','PrivacyR1FinalProtocolBuilder','BuilderPublicExtracted','BuilderPublicProjection']
records=[json.loads(l) for l in (E/'attempts.jsonl').read_text().splitlines()]
latest={r['module']:r for r in records}
final={}; theorem_count=0
for name in mods:
 m='R1Z.'+name;p=ROOT/'docs/research/v8-r0-zk-20261009/lean/R1Z'/(name+'.lean');s=p.read_text();r=latest[m]
 assert r['exit']==0 and r['swaps']=='0' and not r['errors'],m
 assert hashlib.sha256(p.read_bytes()).hexdigest()==r['source_sha256'],m
 clean=re.sub(r'/\-.*?\-/','',s,flags=re.S)
 clean='\n'.join(l for l in clean.splitlines() if not l.lstrip().startswith('--'))
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',clean),m
 if name!='BuilderPublicExtracted':
  assert not re.search(r'set_option (maxHeartbeats|maxRecDepth)',s),m
 for t in re.findall(r'^theorem (\w+)',s,re.M):
  assert any('.'+t+"'" in a for a in r['axioms']),(m,t)
  theorem_count+=1
 for a in r['axioms']:
  match=re.search(r'\[([^]]*)\]',a)
  if match:assert {x.strip() for x in match.group(1).split(',')}<={'propext','Classical.choice','Quot.sound'},a
 final[m]=r
script='''import pathlib,hashlib,re,json
J=pathlib.Path('/home/dombarker/project-offloads/aspis-joint-20261019')
env=json.loads(pathlib.Path('/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/env/J.json').read_text())
search=[J/'objects']+[pathlib.Path(p) for p in env['LEAN_PATH'].split(':')]
def pin(p):return {'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'size':p.stat().st_size} if p.exists() else {'sha256':'missing','size':None}
out={}
for m in MODS:
 p=J/'sources'/(m.replace('.','/')+'.lean')
 deps={d:pin(J/'objects'/(d.replace('.','/')+'.olean')) for d in sorted(re.findall(r'^import (\\S+)',p.read_text(),re.M))}
 fp=hashlib.sha256(';'.join(d+'='+v['sha256'] for d,v in deps.items()).encode()).hexdigest()[:16]
 resolved={}
 for d in deps:
  q=next((root/(d.replace('.','/')+'.olean') for root in search if (root/(d.replace('.','/')+'.olean')).exists()),None)
  assert q is not None,d
  resolved[d]={'path':str(q),**pin(q)}
 out[m]={'resolved_imports':resolved,'source':pin(p),'object':pin(J/'objects'/(m.replace('.','/')+'.olean')),'direct_imports':deps,'deps_fingerprint':fp}
print(json.dumps(out))
'''.replace('MODS',repr(list(final)))
pins=json.loads(subprocess.check_output(['ssh','dombarker@100.108.41.90','python3 -'],input=script,text=True))
for m,r in final.items():
 assert pins[m]['source']['sha256']==r['source_sha256'],m
 assert pins[m]['deps_fingerprint']==r['deps_fingerprint'],m
 pins[m].update({k:r[k] for k in ['attempt','source_revision','source_dirty','exit','wall','peak_rss_kib','swaps','axioms']})
base='5f877a406'
protected=['docs/research/v8-r0-zk-20261009/lean/R1Z/PrivacyR1Final.lean','docs/research/v8-r0-zk-20261009/lean/R1Z/PrivacyR1FinalProtocol.lean']
for p in protected:
 assert (ROOT/p).read_bytes()==subprocess.check_output(['git','show',base+':'+p],cwd=ROOT),p
shipped_diff=subprocess.check_output(['git','diff',base,'--','crates'],cwd=ROOT,text=True)
assert not shipped_diff,'shipped source changed: requires all three ELF rebuilds'
# Retain D89 couplings and all binders except derived hpub / builder soundness.
s0=(ROOT/protected[1]).read_text();p=ROOT/'docs/research/v8-r0-zk-20261009/lean/R1Z/PrivacyR1FinalProtocolBuilder.lean';s1=p.read_text()
def signature(s,t):
 start=s.index('theorem '+t+'\n');return s[start:s.index(' := by\n',start)]
before=signature(s0,'privacy_R1_protocol')
after=signature(s1,'privacy_R1_protocol_source')
expected=before.replace('theorem privacy_R1_protocol\n','theorem privacy_R1_protocol_source\n').replace('(builder_refinement_D46_D51 : R0Z.HonestValidity.BuilderSoundOn h B x)','(runtime_join : BuilderRuntimeJoin.RustRuntimeJoin h)')
expected=expected.replace(' (hpub : PublicBase F x.1)','')
assert after==expected,'unintended source-facing premise or conclusion change'
canon=signature(s1,'privacy_R1_protocol_builder')
expected_canon=before.replace('theorem privacy_R1_protocol\n','theorem privacy_R1_protocol_builder\n').replace('    (builder_refinement_D46_D51 : R0Z.HonestValidity.BuilderSoundOn h B x)\n','').replace('h.Instance','(h).Instance').replace('h.public','(h).public').replace('h.transport','(h).transport')
expected_canon=expected_canon.replace(' (hpub : PublicBase F x.1)','')
assert canon==expected_canon,'unintended canonical endpoint signature change'
raw=(ROOT/'docs/research/v8-r0-zk-20261009/lean/R1Z/BuilderPublicExtracted.lean').read_text().replace('import Aeneas.Std\nimport Aeneas.Tactic.RustAttributes\n','import Aeneas\n').replace('inductive pool_v1.pair_forest_semantic_terminal.CompiledVariant','@[discriminant isize]\ninductive pool_v1.pair_forest_semantic_terminal.CompiledVariant')
extract=json.loads((E/'public-extraction.json').read_text())
assert hashlib.sha256(raw.encode()).hexdigest()==extract['public-extraction/generated/Public.lean']['sha256'],'semantic edit to generated source'
summary={'source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
 'theorem_count':theorem_count,'attempts':len(records),'modules':pins,'protected_unchanged':protected,
 'shipped_crate_diff_empty':True,'signature_comparisons':'exact; canonical h fixed; builder soundness discharged or replaced by runtime join; hpub derived on honest fibres in both; other binders and conclusions unchanged',
 'full_frozen_manifest':'not replayed; no frozen module changed, no deployed/release source closure claimed'}
(E/'final-audit.json').write_text(json.dumps(summary,indent=2)+'\n')
print('PASS:',theorem_count,'theorems;',len(records),'retained attempts;',len(mods),'current modules; standard axioms; zero swaps')
