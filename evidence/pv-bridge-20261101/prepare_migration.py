"""Stage new-name privacy import routes; never edit an existing source or object."""
from pathlib import Path
import json,hashlib,re,subprocess
B=Path(__file__).resolve().parent;R=B.parent.parent
S=json.loads((B/'SELECTED-SOURCES.json').read_text());G={r['module']:r['imports'] for r in json.loads((B/'IMPORT-PLAN.json').read_text())['modules']}
for m,v in S.items():assert hashlib.sha256(v['text'].encode()).hexdigest()==v['sha256'],m
bundle={m for m in S if m.startswith('PV_2TNV_')}
name={m:('PV_BR_FixtureBundle' if m in bundle else 'PV_BR_'+m.replace('.','_')) for m in S}
name['R1Z.BuilderAdmissionExtracted']='PV_BR_BuilderAdmission';name['AspisR1ProverCommit.Types']='PV_BR_ProverTypes'
for m in ['R1Z.PV_RJDec_V047Native','PV_RJ4IDB_CallerPublic','PV_RJ4IDB_CallerLive']:name[m]='PV_BR_CallerShared'
provider_route={r['privacy']:r['canonical'] for r in json.loads((B/'FIXTURE-PROVIDER-REBASE.json').read_text())['pairs']}
provider_route['PV_2TNV_ByteEncoding']='PV_BR_ByteEncoding'
# Topological order, retaining the 95 recorded historical import edges.
order=[]
while len(order)<len(G):
 ready=sorted(m for m in G if m not in order and not ((set(G[m])&G.keys())-set(order)))
 assert ready,'source graph cycle';order+=ready
edges={name[m]:set() for m in G}
for m,ds in G.items():edges[name[m]]|={name[d] for d in ds if d in G and name[d]!=name[m]}
qorder=[]
while len(qorder)<len(edges):
 ready=sorted(m for m in edges if m not in qorder and edges[m]<=set(qorder))
 assert ready,'module grouping introduces a dependency cycle';qorder+=ready
D=B/'draft-migration';D.mkdir(exist_ok=True)
manifest=[]
for new in qorder:
 members=[m for m in order if name[m]==new]
 if new in ['PV_BR_BuilderAdmission','PV_BR_ProverTypes']:
  manifest.append({'module':new,'members':members,'path':str(B/f'{new}.lean'),'sha256':hashlib.sha256((B/f'{new}.lean').read_bytes()).hexdigest(),'status':'UNCOMPILED'});continue
 imports=[];bodies=[]
 for m in members:
  s=S[m]['text'];raw=s
  imps=re.findall(r'^import ([^\n]+)\n',s,re.M)
  for line in imps:
   for imp in line.split():
    routed=name.get(imp,provider_route.get(imp,imp))
    if routed!=new and routed not in imports:imports.append(routed)
  s=re.sub(r'^import [^\n]+\n','',s,flags=re.M)
  assert not re.search(r'^(?:public |meta )?import\b',s,re.M),'unhandled import syntax'
  if len(members)>1:
   stack=[]
   for l in s.splitlines():
    t=l.strip()
    if re.match(r'(noncomputable\s+)?section\b|namespace\b',t):stack.append(t)
    elif re.match(r'end(?:\s|$)',t):stack.pop()
   assert all(t in ['noncomputable section','section'] for t in stack),(m,stack)
   s='section\n'+s+'\n'+('end\n'*len(stack))+'end\n'
  bodies.append(f'/- Original source module {m}; sha256 {S[m]["sha256"]}. -/\n'+s)
 text=''.join('import '+i+'\n' for i in imports)+'\n'+'\n'.join(bodies)
 p=D/f'{new}.lean';p.write_text(text)
 manifest.append({'module':new,'members':members,'source_records':{m:{k:v for k,v in S[m].items() if k!='text'} for m in members},'path':str(p),'sha256':hashlib.sha256(text.encode()).hexdigest(),'imports':imports,'status':'UNCOMPILED'})
(B/'MIGRATION-MANIFEST.json').write_text(json.dumps({'modules':manifest,'affected_original_modules':95,'new_migration_modules':len(manifest),'unchanged_ndr_modules':True,'fixture_provider_rebase':'FIXTURE-PROVIDER-REBASE.json', 'budget_plan':{'historical_attempts_used':74,'remaining_plan':5,'expected_cumulative':79,'additional_module':'PV_BR_ByteEncoding','migration':len(manifest),'adapter':1,'transport':1,'admission_transport':1,'both_closure_smoke':1,'audit':1,'total_if_first_attempt_passes':len(manifest)+6,'maximum':80},'bundle_justification':'29 small fixture modules (271500 source bytes) form an acyclic quotient. No theorem text is changed. Imports move to the module header; section wrappers restore original end-of-file local scopes. This is a draft proof-module grouping, not a validated module-equivalence claim.'},indent=2)+'\n')
(B/'PV_BR_ConsumerImportSmoke.lean').write_text('''import PV_BR_PV_EVH_Deployed
import PV_BR_CallerShared
import PV_BR_AdmissionTransport
import NDR_CombinedAudit

/-! Both complete closures through the privacy bridge. UNCOMPILED until receipted. -/
#check PV_BR_AdmissionTransport.validateCommon_success
#check R1Z.PV_RJ4IDB_CallerLive.caller_witness
#check AspisR1.NDR_CombinedAudit.sourceOnHeadline
#print axioms PV_BR_AdmissionTransport.validateCommon_roundtrip
#print axioms R1Z.PV_RJ4IDB_CallerLive.caller_witness
#print axioms AspisR1.NDR_CombinedAudit.sourceOnHeadline
''')
raw=subprocess.check_output(['git','show','HEAD:lean/PV_EVH_FixtureConsumer.lean'],cwd=R).decode()
for old in ['PV_EVH_Deployed','PV_RJ4IDB_CallerLive']:raw=raw.replace('import '+old+'\n','import '+name[old]+'\n')
if 'import PV_BR_AdmissionTransport\n' not in raw:raw='import PV_BR_AdmissionTransport\n'+raw
audit=[l for l in (B/'PV_BR_Audit.lean').read_text().splitlines() if l.startswith('#print axioms ')]
raw+='\n/- Lead-only consumer plus combined audit; NOT LAUNCHED. -/\n'+'\n'.join(audit)+'\n'
(B/'PV_BR_FixtureConsumer.lean').write_text(raw)
obsolete=['PV_BR_R1Z_PV_RJDec_V047Native','PV_BR_PV_RJ4IDB_CallerPublic','PV_BR_PV_RJ4IDB_CallerLive']
for n in obsolete:
 p=D/f'{n}.lean'
 if p.exists():p.unlink()
print('Prepared',len(manifest),'migration modules; source text unchanged except routing/scopes; UNCOMPILED')
