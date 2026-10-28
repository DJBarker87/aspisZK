from auditlib7 import *
def discover(k,ps):
 q=subprocess.run(['git','grep','-l','-e','.',pins[k],'--',*ps],capture_output=True,text=True)
 return [l.split(':',1)[1] for l in q.stdout.splitlines()]
patterns={
'rw':['evidence/pv-batch3-20261027/lean/PV_B3_*.lean','evidence/pv-batch3-20261027/STRUCTURAL*D336.json','evidence/pv-batch3-20261027/d336*.json','evidence/pv-batch2-20261027/batch2f/V*.json','evidence/pv-batch2-20261027/batch2f/*BINDING.json','evidence/pv-batch2-20261027/batch2f/FINAL*.json','evidence/pv-batch2-20261027/batch2f/PREMISE-DELTA.json','evidence/pv-relink-20261028/V*/row.json','evidence/pv-relink-20261028/*binding.json','evidence/pv-relink-20261028/final.json','evidence/pv-relink-20261028/lean/PV*.lean'],
'runjoin':['docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RunJoin_*24.lean','docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RunJoin_*25.lean','docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RunJoin_*26.lean','docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RunJoin_*27.lean','docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RunJoin_*28.lean','evidence/pv-runjoin31-20261028/LANE-STATEMENT-AUDIT.md','evidence/pv-runjoin31-20261028/STAGE*.md','evidence/pv-runjoin31-20261028/recovery/*.md'],
'research':['evidence/pv-kscan-20261028/*.json','evidence/kani-mitig-20261028/KMX_FINDING.md','evidence/kani-reverify1-20261028/KMY_FINDING.md','evidence/kani-reverify2-20261028/KMZ_FINDING.md']}
for k,ps in patterns.items():
 for path in discover(k,ps):read(k,path)
for k in ['rw','research']:
 for m in ['R0Z.FsStatement','R0Z.JointView','R0Z.ZkStatement','R1Z.RomObserverBin','R1Z.PrivacyR1HeadlineDeployedReal','R1Z.ProverCommitFuelJoin22']:
  module(k,m)
# Reference complete statements, definitions and selected constructors, recursively.
queue=[('rw','PV_B3_'+n) for n in ['Close134','Install222','Install117','Install121','FlatInstallD336']]
queue += [('rw','R1Z.PV_B2_F_AuditClosure'),('rw','R1Z.PV_AL_MoveClosure')]
queue += [('runjoin','R1Z.PV_RunJoin_'+n) for n in ['HonestIdentification26','HonestConsumer26','HonestFixtures26','PaddingCounterexample24']]
seen=set();cones=[]
for k,m in queue:
 if (k,m) in seen:continue
 seen.add((k,m));s,path=module(k,m)
 if not s:continue
 cones.append(dict(ref=k,module=m,path=path,sha256=hashlib.sha256(s.encode()).hexdigest()))
 for dep in re.findall(r'^import\s+(\S+)',s,re.M):
  if dep.startswith(('PV_B3_','R1Z.PV_B2_','R1Z.PV_AL_Move','R1Z.PV_RunJoin_','R1Z.PV_Src_')):queue.append((k,dep))
# Exact source statements, excluding generated field-frame boilerplate.
statements=[]
for x in cones:
 s=read(x['ref'],x['path']);parts=re.split(r'(?m)(?=^(?:theorem|def|abbrev|structure)\s)',s)
 ds=[]
 for a in parts:
  hit=re.match(r'(theorem|def|abbrev|structure)\s+(\S+)',a)
  if hit and not hit[2].startswith('preserved'):
   ds.append(a.split(':=',1)[0].rstrip())
 statements.append({**x,'declarations':ds})
(P/'closing-statements7.json').write_text(json.dumps(statements,indent=2)+'\n')
(P/'closing-source-cones7.json').write_text(json.dumps(cones,indent=2)+'\n')
# Audit existing receipts. Keep complete raw receipt and stdout/time in snapshots.
rs=[('rw',f'evidence/pv-batch3-20261027/receipts/lean-{n}/receipt/receipt.json') for n in [40597,40549,40599]]
rs += [('rw',f'evidence/pv-batch2-20261027/batch2f/{n}.json') for n in [40800,40897,40898]]
rs += [('rw',f'evidence/pv-relink-20261028/{n}/receipt.json') for n in [43799,43731]]
rs += [('runjoin',f'evidence/pv-runjoin26-20261027/receipt-{n}.json') for n in [38135,38137,38138,38140]]
audit=[]
for k,path in rs:
 s=read(k,path);assert s,(k,path);v=json.loads(s)
 audit.append(dict(ref=k,path=path,receipt=v))
 # Receipt schemas differ; collect adjacent full logs if available.
 if 'batch3' in path:
  for f in ['stdout.log','time.log']:read(k,path.rsplit('/',1)[0]+'/'+f)
 elif 'relink' in path:
  for f in ['output.log','time.log']:read(k,path.rsplit('/',1)[0]+'/'+f)
 elif 'runjoin' in path:
  n=re.search(r'receipt-(\d+)',path)[1]
  for f in ['out-'+n+'.log','time-'+n+'.log']:read(k,path.rsplit('/',1)[0]+'/'+f)
(P/'reused-receipts7.json').write_text(json.dumps(audit,indent=2)+'\n')
(P/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print('captured',len(manifest),'cone modules',len(cones),'receipt audits',len(audit))
for a in audit:
 v=a['receipt'];print(a['path'],list(v)[:20])
