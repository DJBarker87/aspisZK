from audit12 import *
manifest.update({x['ref']+':'+x['path']:x for x in json.loads((P/'manifest.json').read_text())})
k=json.loads((P/'k4-credit-check.json').read_text());status={x['credit_id']:x['k4_status'] for x in k['historical_credits']}
support=json.loads((B/'recount11/k3-audit11.json').read_text())['current_support_rows'];rows={r['id']:r for r in json.loads((P/'rows12.json').read_text())}
for r in support:
 id=r['ledger_row'];r['prior_kani_support']=r.get('current_kani_support',[])[:]
 bad=[c for c in r['prior_kani_support'] if status[c]=='SUSPENDED'];r['k4_excluded']=bad
 if bad:
  assert id in ['V177','V180'],(id,bad)
  assert rows[id]['recount12_status']=='OPEN'
  r['current_kani_support']=[];r['current_credited_scope']='Historical source/model law only; selected P6 closure suspended under k4'
 if id=='V233':r['current_credited_scope']='Recount11 exact typed structural consumed_instance restoration; historical C002/C088/C089 excluded';r['basis']='Recount11 typed restoration supersedes historical K3-ROWS wording; independent own-1 route'
 r['depends_on_still_suspended_credit']=any(status[c]=='SUSPENDED' for c in r.get('current_kani_support',[]))
 assert not r['depends_on_still_suspended_credit']
(P/'current-support12.json').write_text(json.dumps(support,indent=1)+'\n')
# Actual full-width declarations in the native proof sources; classification is
# a reviewed source argument, not a regex proof of absence.
source_screens=[]
for ref in ['b3p6','stx','stxb','evhB']:
 for path in tree(ref):
  candidate=(path.startswith('tools/pv-'+ref+'-') if ref!='stxb' else path.startswith('evidence/pv-stxb-20261104/certificate/'))
  if not candidate or not path.endswith('.rs'):continue
  s=txt(ref,path)
  if 'kani::' not in s:continue
  findings=[{'line':i,'text':l} for i,l in enumerate(s.splitlines(),1) if ('usize' in l or '.add(' in l or '.get(' in l) and ('kani::' in l or '.add(' in l or '.get(' in l)]
  source_screens.append({'ref':ref,'revision':revs[ref],'path':path,'sha256':hashlib.sha256(s.encode()).hexdigest(),'fullwidth_and_pointer_sites':findings})
(P/'source-screen12.json').write_text(json.dumps(source_screens,indent=1)+'\n')
# Keep exact negative summaries, sources, and trace path inventories for the
# conservative historical review. No missing trace can become a PASS.
control_paths={'C044':('k3scan','evidence/pv-k3scan-20261101/host/K79201/output.log'),'C084':('runjoin','evidence/pv-kstub-20261028/K13/output.log'),'C088':('k3scan','evidence/pv-k3scan-20261101/host/K79221/output.log'),'C089':('k3scan','evidence/pv-k3scan-20261101/host/K79223/output.log')}
for z in k['historical_credits']:
 if z['credit_id'] not in control_paths:continue
 ref,path=control_paths[z['credit_id']];s=txt(ref,path)
 z['retained_summary']={'ref':ref,'revision':revs[ref],'path':path,'sha256':hashlib.sha256(s.encode()).hexdigest(),'tail':s[s.rfind('Checking harness'):]}
 z['trace_path_inventory']=[p for p in tree(ref) if p.startswith(path.rsplit('/',1)[0]+'/') and re.search('trace',p,re.I)]
 assert not z['trace_path_inventory']
k['current_support']='current-support12.json';k['source_screen']='source-screen12.json'
(P/'k4-credit-check.json').write_text(json.dumps(k,indent=1)+'\n');save()
print('current support checked; source files',len(source_screens))
