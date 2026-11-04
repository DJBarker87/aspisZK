from audit11 import *
manifest.update({x['ref']+':'+x['path']:x for x in json.loads((P/'manifest.json').read_text())})
def get(k,p):
 s=txt(k,p);assert s is not None,(k,p);return s
checks=json.loads(get('rw','evidence/pv-rdcd7-20261102/CONSUMER-RECHECKS.json'))
covered={x['consumer'] for group in ['focused','unchanged','audit_query_projections'] for x in checks[group]}
covered.update(['PV_RDCD5_FocusedReplay','PV_RDCD5_FrozenManifest','PV_RDCD5_NEPDriver','PV_RDCD5_V197Audit','PV_RDCD5_V197Focused','PV_RDCD5_V197FrozenManifest'])
dispositions=[]
for k in revs:
 scan=P/('consumer-scan-'+k+'.txt')
 if not scan.exists():continue
 paths=sorted({x.split(':',2)[1] for x in scan.read_text().splitlines()})
 for p in paths:
  s=get(k,p);record={'ref':k,'path':p,'sha256':hashlib.sha256(s.encode()).hexdigest()}
  if p.endswith('.lean') and '/lean/R1Z/' in p:
   name=Path(p).stem;assert name in covered,(k,p)
   same=s==get('rw',p)
   record['disposition']='Corrected candidate: focused receipt, exact audit projection, unchanged cone or final audit wrapper, per CONSUMER-RECHECKS.' if same else 'Historical branch variant. Not silently re-credited as corrected; current restoration uses candidate sources only. Old owned-parser/kind diagnostics were not restored row credit.'
  else:record['disposition']='Evidence/tooling source or generated query text; no independent native parser/whole-row credit.'
  dispositions.append(record)
res=get('b3p6','evidence/pv-b3p6-20261028/lean/PV_B3P_BridgeResidual557227.lean');assert '(wrapper : DeployedWrapper557 base ops)' in res
h=get('b3p6','evidence/pv-b3p6-20261028/resume18/HANDOFF.md');assert '484/528' in h and '44' in h and 'DeployedWrapper557 is NOT discharged' in h
l3=get('evh','evidence/pv-evh10-20261102/L3-RESIDUAL.md');assert 'ActualEntropyEntryPrefix source-to-machine carrier' in l3 and 'NOT a premise' in l3
block=get('evh','evidence/pv-evh10-20261102/BLOCKER-D588.md');stx=get('stx','evidence/pv-stx-20261104/STATUS.md');assert 'five deployed projection equations do not exist' in stx
b=get('evhB','evidence/pv-evhB-20261103/HANDOFF.md');assert 'advancing world selection remain unproved' in b
# Old K3 support packets are identical to recount10; its independent pair audit remains reusable.
prior=json.loads((B/'recount10/manifest.json').read_text());reuse=[]
for p in ['evidence/pv-k3scan-20261101/CREDITS.json.xz','evidence/pv-k3scan-20261101/K3-ROWS.json']:
 data=read('k3scan',p);old=next(x for x in prior if x['ref']=='k3scan' and x['path']==p);assert hashlib.sha256(data).hexdigest()==old['sha256'];reuse.append({'path':p,'sha256':old['sha256'],'disposition':'Byte-identical prior scoped pair audit reused, D592 overlay applied separately.'})
(P/'status-audit11.json').write_text(json.dumps({'consumer_dispositions':dispositions,'no_new_uninventoried_direct_source_consumer':True,'op227':'OPEN;484/528 local guards,44 indices remain; actual DeployedWrapper557 binder retained, local guards are not native-pointer/caller associations','L3_residual_source':l3,'source_world_blocker':block,'stx_status':stx,'evhB_status':b,'K3_reused_packets':reuse,'new_counted_rows':0},indent=1)+'\n');save();print('PASS direct source consumers',len(dispositions),'current residuals and K3 packet identity')
