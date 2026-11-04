from audit11 import *
manifest.update({x['ref']+':'+x['path']:x for x in json.loads((P/'manifest.json').read_text())})
rows=json.loads((B/'recount10/rows10.json').read_text());by={x['id']:x for x in rows};audit=json.loads((P/'independent-audit11.json').read_text());k3=json.loads((P/'k3-audit11.json').read_text())
for r in rows:
 r['recount10_bucket']=r['dependency_bucket'];r['recount11_status']=r['recount10_status'];r['recount11_class']=r['recount10_class'];r['recount11_basis']='Retain recount10 scoped derivation and residuals for unchanged defining bytes; current global qualifications in METHOD11.md apply.'
 r['definition_witnesses11']='definition-audit11.json#'+r['id'];r['import_witnesses11']='import-membership11.json#'+r['id'];r['recount11_evidence']=['../recount10/rows10.json#'+r['id'],r['definition_witnesses11']]
common='Qualified source/typed complete-Result boundary only; structural own-1/k-prime and existing tool/compiler trust. E1/E2, native RunJoin/world/carrier, runtime/allocator adequacy, V370, actual L1/diag/L3, coherent final replay and non-emptiness remain. Client release adopted separately; no endpoint premise removed.'
restore={
'V233':('R1Z.PV_RDCD5_V233.consumed_instance','Original Eager64 typed split for every valid Slice and logical origin; encode/flatten inverse, typed roundtrip/injectivity, original pointer/count/tail/alias geometry and consumed callback. Complete Result, not byte equality alone.'),
'V236':('R1Z.PV_RDCD5_V236.op216_instance','Original safe Eager64 length64/pos<64 domain, typed callback and arbitrary Slice. All short/first-block/bulk/suffix branches, dead bytes, cursor truncation, ordered typed batches and callback errors/divergence retained. No singleton-fold or extra callback premise.'),
'V197':('R1Z.PV_RDCD5_V197Restored.parser_instance','Every original Slice, complete Result(Option QM31), actual checked borrowed-window transport. Parser-specific invalid range now panic, matching source; same ordered bounds/window and first-None-before-late-range evaluation. No length16/success restriction or error erasure. All15 affected source consumers rechecked; audit projections and unchanged V233/V236 dependencies dispositioned. Wrong-kind local diagnostics explicitly corrected; no restored row relied on wrong kind.')}
for id,(th,s) in restore.items():
 r=by[id];r['recount10_closure_theorem']=r.get('closure_theorem');r['recount10_closure_route']=r.get('closure_route');r['recount11_status']='CLOSED-ON-CANDIDATE';r['dependency_bucket']=None;r['closure_theorem']=th;r['closure_route']='own-1/k-prime structural source binding plus complete typed Result Lean transport';r['recount11_basis']='CONFIRM RESTORATION. '+s+' '+common;r['recount11_evidence']+=['independent-audit11.json#'+id,'receipt-audit11.json'];r['closure_source_module11']='.'.join(th.split('.')[:2])
by['V396']['recount11_basis']='OPEN b. User client fc8808eb is ADOPTED at8897074612 and present in candidate d4ed1ba89f. All client release gates pass, including final timing, owner D575(A) no-core startup and D576(B) alias-safe212-byte output pipe. Entry is parametric22 carriers/105 operations; native startup/pipe/OS effects, upload/caller/observer and joint world integration remain. Client adoption is a deployment-condition improvement, not closure of this integration row.'
by['V178']['recount11_basis']='OPEN b. panic=abort performs no unwinding cleanup. D575(A) adopted non-dumpability/core0 removes readable core-image branch by construction at this client configuration; finite early/post-wallet panic gates pass. Source abort/world/physical interpretation still needs binding; do not infer stack wiping on abort.'
by['V373']['recount11_basis']='OPEN a. Prior whole-kernel disassembly coverage was incomplete. D581-D587 binary-structural entropy/frame evidence is scoped to da36d6aa and does not supply a whole fc8808eb client audit. ActualEntropyEntryPrefix source-to-machine carrier (V370/L3) remains named/unproved; binary refresh/binding required.'
by['V374']['recount11_basis']='OPEN a. Final paired throttled throughput gate passes at fc8808eb, but is not statistical leakage/dudect or universal latency evidence. Decoder trace finite scope retained; whole-client leakage evidence missing.'
for id in ['V241','V244','V245']:
 by[id]['recount11_basis']='OPEN/PARTIAL. op227 local associations and formatting certificates do not discharge PV_B3P_Closure557227.DeployedWrapper557 base ops. Current bounded Kani support C155/C157 is clear of K-3; C163/C164 historical sums restored separately, C156 stays SUSPENDED. Pointer/drop/initializer/caller/native world and complete coverage remain.'
for id in ['V045','V046','V047','V038','V163','V165','V167','V268','V269','V270','V397','V398','V399']:
 by[id]['recount11_basis']+=' Current composition note: NER coherent base rebuilt;92060 consumer+zero-dangling scan passes but raw driver fails before traversal, so joint three-step gate does NOT count. No coherent actual non-vacuity witness credited. Event-world/source links remain ordinary P.'
for id in ['V183','V228','V263','V225','V400']:
 by[id]['recount11_basis']+=' Current source interpreter/world associations remain uninstalled. OS/allocator/thread/stack failure branches retained under rdea-2/rdea-2-prime; success granting-world witnesses do not establish witness-independent failures. No T field.'
for r in k3['current_support_rows']:
 if r['ledger_row'] in by:by[r['ledger_row']]['k3_current_scope11']='k3-audit11.json#'+r['ledger_row']
# Recompute exact same historical consumer roots. Parked roots keep historical pins.
oldpins=json.loads((B/'recount10/pins.json').read_text())['revisions'];hist={}
roots=[(x['ref'],x['root']) for x in json.loads((B/'recount10/import-closures10.json').read_text()) if not x.get('new_endpoint')]
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
 th=r.get('closure_theorem') if r['recount11_status']=='CLOSED-ON-CANDIDATE' else None
 if th:
  m=next((r.get('closure_source_module'+str(i)) for i in [11,10,9,8,7,6] if r.get('closure_source_module'+str(i))),None)
  m=m or ('.'.join(th.split('.')[:2]) if th.startswith('R1Z.') else th.split('.')[0])
 else:
  d=r.get('definition','').split('#')[0];m=('R1Z.'+Path(d).stem if '/lean/prover-rw-' in d else d.split('/lean/')[-1][:-5].replace('/','.')) if '/lean/' in d and d.endswith('.lean') else None
 ws=[];new=[]
 if m:
  source,p=module('rw',m)
  if th:
   assert source is not None,(r['id'],m)
   r['closing_statement11']={'ref':'rw','revision':revs['rw'],'module':m,'path':p,'sha256':hashlib.sha256(source.encode()).hexdigest(),'theorem':th}
  for cl in closures:
   if m not in cl['paths']:continue
   s,_=module(cl['ref'],m);norm=lambda t:re.sub(r'^import[^\n]*\n','',t,flags=re.M)
   if not th or (s and source and norm(s)==norm(source)):
    w={'ref':cl['ref'],'root':cl['root'],'path':cl['paths'][m],'scope':'import membership, not discharge'};(new if cl['new_endpoint'] else ws).append(w)
 members.append({'id':r['id'],'module':m,'witnesses':ws,'event_endpoint_witnesses':new})
 r['in_headline_closure11']='research' if any(w['ref']=='research' for w in ws) else 'candidate' if ws else 'neither'
 if r['recount11_status']!='OPEN':r['dependency_bucket']=None
 else:assert r['dependency_bucket'] in 'abcd'
(P/'import-membership11.json').write_text(json.dumps(members,separators=(',',':'))+'\n');(P/'import-closures11.json').write_text(json.dumps(closures,separators=(',',':'))+'\n')
(P/'rows11.json').write_text('[\n'+',\n'.join(json.dumps(r,separators=(',',':')) for r in rows)+'\n]\n')
t={'rows':len(rows),'classes':dict(collections.Counter(r['recount11_class'] for r in rows)),'statuses':dict(collections.Counter(r['recount11_status'] for r in rows)),'open_dependencies':dict(collections.Counter(r['dependency_bucket'] for r in rows if r['recount11_status']=='OPEN')),'all_row_imports':dict(collections.Counter(r['in_headline_closure11'] for r in rows)),'restored':list(restore),'status_changes':[{'id':r['id'],'before':r['recount10_status'],'after':r['recount11_status'],'reason':r['recount11_basis']} for r in rows if r['recount10_status']!=r['recount11_status']],'bucket_changes':[],'k3_credits':k3['counts'],'k3_status_changes':[{'id':c['credit'],'before':'SUSPENDED','after':c['status']} for c in k3['changes'] if c['status']=='RESTORED'],'client_release':'ADOPTED fc8808eb; every release gate passes; native integration OPEN','endpoint_premises_removed_added_weakened':[0,0,0],'Lean':0,'Lean_budget':40,'Kani':0,'Env_J':'92100-92139 unused','target':'Target not yet established','historical_parked_roots':hist}
(P/'totals.json').write_text(json.dumps(t,indent=2)+'\n');save()
ls=['# Recount 11 2026-11-04 (B)','','All407 rows; current fields supersede dated historical wording. Same columns/buckets as recount10; historical evidence retained in rows11.json. Membership is not discharge. Target not yet established.','','| Row / class10 →11 / name | Status10 →11 | OPEN bucket | in headline closure? | Tool trust | Derivation, residual and evidence |','|---|---|---|---|---|---|']
for r in rows:
 detail=r['recount11_basis']+' Historical scoped derivation/residual: recount11/rows11.json#'+r['id']+'; '+r['definition_witnesses11']
 ls.append('|'+r['id']+' / '+r['recount10_class']+' → '+r['recount11_class']+' / '+r['name'].replace('|','\\|')+'|'+r['recount10_status']+' → '+r['recount11_status']+'|'+(r['dependency_bucket'] or '—')+'|'+r['in_headline_closure11']+'|'+r['tool_trust10']+'|'+detail.replace('|','\\|').replace('\n',' ')+'|')
(B/'ROWS11.md').write_text('\n'.join(ls)+'\n');print(json.dumps(t,indent=2))
