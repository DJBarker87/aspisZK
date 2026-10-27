import pathlib,re,hashlib,json,sys
root=pathlib.Path('docs/research/v8-r0-zk-20261009/lean/R1Z')
groups={
'Model':['OffBad','Charged','OffPole','AlignedSchedule'],
'Source':['OffBadJoin','BodySync','DeployedOffBad','WorldFrames','FirstFailureOffBad','ProjectionBoundary'],
'Endpoint':['JointTransport','Correlation','BoundComposition']}
manifest=[]
for group,names in groups.items():
 imports=['import R1Z.PV_OptB_'+n for n in names]
 if group=='Endpoint':imports+=['import R1Z.PV_OptB_Endpoint']
 lines=imports+['set_option autoImplicit false']
 for name in names:
  p=root/('PV_OptB_'+name+'.lean');s=p.read_text();ns=re.search(r'^namespace (\S+)',s,re.M)[1]
  assert not re.search(r'\b(?:sorry|admit|native_decide|implemented_by)\b|^axiom\s|set_option\s+(?:maxHeartbeats|maxRecDepth)',s,re.M),p
  for decl in re.findall(r'^(?:theorem|def|abbrev)\s+(\w+)',s,re.M):lines+=['#print axioms '+ns+'.'+decl]
  manifest.append(dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size))
 if group=='Source':
  lines+=['#print R1Z.PV_OptB_OffBadJoin.Steps','#print R1Z.PV_OptB_DeployedOffBad.conditional_off_bad','#print R1Z.PV_RunJoin_UnifiedRetry.BodySourceLaw']
 if group=='Endpoint':
  lines+=['#print R1Z.PrivacyR1HeadlineDeployedReal.RustRealRefinement','#print R1Z.PV_OptB_Endpoint.privacy_headline_deployed_B','#print axioms R1Z.PrivacyR1HeadlineDeployedReal.privacy_headline_deployed','#print axioms R1Z.PV_OptB_Endpoint.privacy_headline_deployed_B']
 out=root/('PV_OptB_OffBadAudit'+group+'.lean');expected='\n'.join(lines)+'\n'
 if '--check' in sys.argv:assert out.read_text()==expected,out
 else:out.write_text(expected)
 if '--check' in sys.argv:manifest.append(dict(path=str(out),sha256=hashlib.sha256(out.read_bytes()).hexdigest(),bytes=out.stat().st_size))
if '--check' in sys.argv:
 pathlib.Path(__file__).with_name('source-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
 print('Audit source validation passed; no banned proof escape or raised limits.')
