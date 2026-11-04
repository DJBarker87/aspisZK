# Recompute exact same historical consumer roots. Parked roots keep historical pins.
oldpins=json.loads((B/'recount11/pins.json').read_text())['revisions'];oldpins.update(json.loads((B/'recount11/pins.json').read_text()).get('historical_parked_revisions',{}));hist={}
roots=[(x['ref'],x['root']) for x in json.loads((B/'recount11/import-closures11.json').read_text()) if not x.get('new_endpoint')]
for k,_ in roots:
 if k not in revs:revs[k]=oldpins[k];hist[k]=oldpins[k]
closures=[]
for k,root in roots+[('rw','PV_MEAS_Deployed')]:
 paths={root:[root]};queue=[root];missing=[]
 for m in queue:
  if not m.startswith(('R1Z.','R0Z.','PV_')):continue
  s,p=module(k,m)
  if s is None:missing.append(m);continue
  for d in re.findall(r'^import\s+(\S+)',s,re.M):
   if d not in paths:paths[d]=paths[m]+[d];queue.append(d)
 closures.append({'ref':k,'revision':revs[k],'root':root,'new_endpoint':root=='PV_MEAS_Deployed','paths':paths,'unresolved_project_modules':missing})
members=[]
for r in rows:
 th=r.get('closure_theorem') if r['recount12_status']=='CLOSED-ON-CANDIDATE' else None
 if th:
  m=next((r.get('closure_source_module'+str(i)) for i in [12,10,9,8,7,6] if r.get('closure_source_module'+str(i))),None)
  m=m or ('.'.join(th.split('.')[:2]) if th.startswith('R1Z.') else th.split('.')[0])
 else:
  d=r.get('definition','').split('#')[0];m=('R1Z.'+Path(d).stem if '/lean/prover-rw-' in d else d.split('/lean/')[-1][:-5].replace('/','.')) if '/lean/' in d and d.endswith('.lean') else None
 ws=[];new=[]
 if m:
  source,p=module('rw',m)
  if th:
   assert source is not None,(r['id'],m)
   r['closing_statement12']={'ref':'rw','revision':revs['rw'],'module':m,'path':p,'sha256':hashlib.sha256(source.encode()).hexdigest(),'theorem':th}
  for cl in closures:
   if m not in cl['paths']:continue
   s,_=module(cl['ref'],m);norm=lambda t:re.sub(r'^import[^\n]*\n','',t,flags=re.M)
   if not th or (s and source and norm(s)==norm(source)):
    w={'ref':cl['ref'],'root':cl['root'],'path':cl['paths'][m],'scope':'import membership, not discharge'};(new if cl['new_endpoint'] else ws).append(w)
 members.append({'id':r['id'],'module':m,'witnesses':ws,'event_endpoint_witnesses':new})
 r['in_headline_closure12']='research' if any(w['ref']=='research' for w in ws) else 'candidate' if ws else 'neither'
 if r['recount12_status']!='OPEN':r['dependency_bucket']=None
 else:assert r['dependency_bucket'] in 'abcd'
(P/'import-membership12.json').write_text(json.dumps(members,separators=(',',':'))+'\n');(P/'import-closures12.json').write_text(json.dumps(closures,separators=(',',':'))+'\n')
