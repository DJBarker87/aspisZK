"""Freeze only accepted source claims, partition their audit, never replay failed candidates."""
import pathlib,json,hashlib,re,sys,subprocess
R=pathlib.Path(__file__).resolve().parents[2];E=R/'evidence/pv-reach-20261027/resume10';L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rs=[json.load(open(p)) for p in sorted(E.glob('receipt-[0-9]*.json')) if int(p.stem.split('-')[-1])<40497];assert len(rs)==97
proofs=[];failed=[]
for r in rs:
 for m in r['modules']:
  if not m.get('accepted'):
   assert sha(R/m['source']['path'])==m['source']['sha256'],('failed source changed',m['module'])
   failed.append(dict(attempt=r['attempt'],module=m['module'],path=m['source']['path'],sha256=m['source']['sha256'],credit=False));continue
  if r['attempt']<40406 or not m['module'].startswith('R1Z.PV_RE_'):continue
  p=R/m['source']['path'];s=p.read_text();assert sha(p)==m['source']['sha256']
  assert not re.search(r'\b(sorry|admit|axiom|native_decide|implemented_by)\b',s),p
  assert not re.search(r'set_option\s+(maxHeartbeats|maxRecDepth)',s),p
  assert not re.search(r'^import\s+\S*\bXR',s,re.M),p
  names=[]
  for ax in m['axioms']:
   name=re.search(r"'([^']+)'",ax)[1];names.append(name)
   if 'depends on axioms:' in ax:
    vals=[x.strip() for x in ax.split('[',1)[1].split(']',1)[0].replace('\n',' ').split(',')]
    assert all(not x or x in ['propext','Classical.choice','Quot.sound'] for x in vals),ax
  # Every public theorem declared by a candidate has an explicit accepted axiom report.
  namespace=re.search(r'^namespace\s+(\S+)',s,re.M)[1]
  for n in re.findall(r'^theorem\s+(\w+)',s,re.M):assert namespace+'.'+n in names,(p,n,names)
  proofs.append(dict(module=m['module'],path=m['source']['path'],source_sha256=sha(p),object_sha256=m['object_sha256'],attempt=r['attempt'],declarations=names,axioms=m['axioms']))
assert len(proofs)==71,len(proofs)
groups={'A':[],'B':[]}
for p in proofs:groups['B' if any(x in p['module'] for x in ['Client','Native']) else 'A'].append(p)
contents={}
for key,ps in groups.items():
 txt='\n'.join('import '+p['module'] for p in ps)+'\n'
 for p in ps:
  for n in p['declarations']:txt+='#check @'+n+'\n#print axioms '+n+'\n'
 if key=='B':
  for n in ['R1Z.PV_Src_PublicDeploymentAssociation.Association','R1Z.PV_Src_ExternalAssociation.Associated','R1Z.PV_Src_RecordAssociation.Associated','R1Z.PV_Src_NativeIdentification.PV_Src_Premises']:
   txt+='#print '+n+'\n'
 contents[key]=txt
contents['C']='import R1Z.PV_RE_FinalAudit10A\nimport R1Z.PV_RE_FinalAudit10B\n-- Once-only frozen focused import replay; declarations were audited in A/B.\n'
for key,txt in contents.items():
 p=L/('PV_RE_FinalAudit10'+key+'.lean')
 if '--check' in sys.argv:assert p.read_text()==txt
 else:p.write_text(txt)
manifest=dict(proofs=proofs,failed_originals=failed,new_accepted_proof_modules=len(proofs),audits=[dict(attempt=40497+i,module='R1Z.PV_RE_FinalAudit10'+k,path=str((L/('PV_RE_FinalAudit10'+k+'.lean')).relative_to(R)),sha256=hashlib.sha256(contents[k].encode()).hexdigest()) for i,k in enumerate('ABC')],scope='Focused source-prefix, conditional material/native-reference and outcome claims; not universal invocation coverage, native whole-client success, endpoint audit or release rebuild',external_manifest_sha256=sha(E.parent/'resume7/external-object-manifest.json'),h4_preflight_sha256=sha(E/'h4-verification.json'))
p=E/'frozen-proof-manifest.json'
if '--check' in sys.argv:assert json.load(open(p))==manifest
else:p.write_text(json.dumps(manifest,indent=2)+'\n')
print('Frozen:',len(proofs),'accepted proof modules;',sum(len(p['declarations']) for p in proofs),'declarations;',len(failed),'unchanged failed originals; audits 40497–40499.')
