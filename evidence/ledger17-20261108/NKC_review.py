from pathlib import Path
import json,lzma,hashlib,copy
E=Path(__file__).resolve().parent;P=E.parent/'ledger16-20261108'
H=lambda b:hashlib.sha256(b).hexdigest()
def J(p):return json.loads(lzma.decompress(p.read_bytes())if p.suffix=='.xz'else p.read_bytes())
def put(n,x):
 raw=(json.dumps(x,indent=1)+'\n').encode();p=E/n
 if n.endswith('.xz'):p.write_bytes(lzma.compress(raw));Path(str(p)[:-3]+'.sha256').write_text(H(raw)+'\n')
 else:p.write_bytes(raw)
b=J(P/'NJW_LEDGER.json.xz');by={r['row']:r for r in b['rows']}
q=E/'NKC_L002/stdout.log';lines=(q.read_text()if q.exists()else lzma.decompress(Path(str(q)+'.xz').read_bytes()).decode()).splitlines();statements={}
for l in lines:
 if 'NKC_OWNER 'in l:
  x=json.loads(l.split('NKC_OWNER ',1)[1]);assert x['root']not in statements;statements[x['root']]=x
assert len(statements)==len(J(E/'NKC_AUDIT_ROOTS.json')['roots'])
old=J(P/'NJW_KERNEL_STATEMENTS.json.xz');wrong=[r for r in old if old[r]!=statements.get(r)];assert not wrong,wrong[:5]
put('NKC_KERNEL_STATEMENTS.json.xz',statements)
put('NKC_OWNER_COMPARISON.json',dict(status='PASS',predecessor_roots=len(old),identical=len(old),new_roots=len(statements)-len(old),mismatches=wrong))
packets={p['row']:p for p in J(E.parent/'batch-merkle-20261108/NJS_ROW_PACKETS.json')};rows=[]
for folder,pre in J(E/'NKC_SPECS.json')[1:]:
 for f in J(E.parent/folder/f'{pre}_CLOSED.json')['functions']:
  for rid in f['rows']:
   r=by[rid];assert r['status']=='OPEN'and r['function']==f['function'],rid
   for k in ['frozen_body_sha256','obligation_statement_hash']:
    if f.get(k):assert r[k]==f[k],(rid,k)
   baseline_file={'NJS':'NJS_BASELINE_ROWS.json.xz','NJV':'NJV_BASELINE_ROWS.json','NJY':'NJY_BASELINE_ROWS.json.xz'}.get(pre)
   if baseline_file:
    bl=J(E.parent/folder/baseline_file)
    if isinstance(bl,dict):bl=bl.get('rows',list(bl.values()))
    original=next(v for v in bl if v['row']==rid)
    assert original['obligation']==r['obligation'],(rid,'complete baseline obligation differs')
   p=packets.get(rid)
   if p:
    assert p['frozen_body_sha256']==r['frozen_body_sha256']and p['obligation_statement_hash']==r['obligation_statement_hash'],rid
    for c in r['obligation']['caller_domain_obligations']:
     matches=[v for v in p['caller_clauses']if v.get('id')==c['id']]
     assert len(matches)==1,(rid,c['id'])
     for k,v in c.items():
      if k not in ['status','discharged_by','owner_packets']:assert matches[0].get('original_clause',matches[0])[k]==v,(rid,k)
   roots=f['lean_roots'];ks=[statements[n]for n in roots]
   primary=f.get('model_theorem',roots[0])
   if pre=='NJV':primary='NJV_TX1.TX1_127'if rid.startswith('TX1')else'NJV_TX2.TX2_093'
   inv=dict(root_inputs=f['root_domain'],headline_hypotheses=[],reviewed_parent_cuts=[],retained_caller_input_domains=[f['root_domain']],extra_logical_hypotheses=[],endpoint_or_success_premises=[])
   if pre=='NJS':
    detail='Each TX1/TX2 occurrence compared independently against NJW body, obligation hash and complete caller clauses. Total leaf equations or reviewed BatchNative cuts; arbitrary typed carrier/full Result/frame/order. Parent-owned batch/proof/query domains remain explicit.'
    inv['reviewed_parent_cuts']=['NJS native leaf/control or SAME-source one-step cuts, as exact row packet; P6/D188 option A']
   elif pre=='NJT':
    detail='Reviewed RankCut/WordsCut/FinishCut or universal native word-step Cut under (ai)(5)/(aq)(2). Default/SAME-block carries establish all native bounds; full membership prefix/state/Result/stop/frame. Fixed-array8 shape fidelity reviewed separately; no production stub_verified.069/129 remain OPEN.'
    inv['reviewed_parent_cuts']=['Exact NJT_QLeaves or NJT_QReached native cut; NJT_HYPOTHESIS_INVENTORY.md']
   elif pre=='NJV':
    detail='Complete returning AND abort roots at SAME binary-entry input, both mutable arrays and chronological log. <=9216 bytes derived by from_count on SAME counted keys; original d<=10 unit retained at TX1:083, TX2<=12 NOT inferred to imply10. Generic <=16/rejection bridge is used for TX2. Original unit/proof/query/count/padding clauses retained on both parents.'
    inv['reviewed_parent_cuts']=['Reviewed native entry/height/terminal/one-step cuts under(ai)(5)/(aq); SAME child Results internally fixed']
   else:
    item=next(x for x in J(E.parent/folder/'NJY_HYPOTHESES.json')['roots']if rid in x['rows'])
    inv['reviewed_parent_cuts']=item['Prop_inputs'];inv['retained_caller_input_domains']=['All valid immutable typed slices; all lengths/content, no success/canonicality restriction']
    inv['reviewed_transcription']=f['reviewed_transcription']
    detail='(ah)/(ay) source-ordered segment frame chain, every Result/error arm and returned record; one arbitrary step plus finite induction. Per-record fidelity controls verified in NKC_NATIVE_REVIEW.json. Raw helper only; NJY-B1 wrapper slots48/49 remain OPEN; registry31/entry32 installation preserves digest/error43/44.'
   cls={k:copy.deepcopy(r['obligation'][k])for k in ['named_hypotheses','inventory_domain_obligations','caller_domain_obligations']}
   rows.append(dict(row=rid,provider=pre,function=r['function'],basis_obligation_statement_hash=r['obligation_statement_hash'],frozen_body_sha256=r['frozen_body_sha256'],certificate=f,root_domain=f['root_domain'],roots=roots,primary_root=primary,original_clauses=cls,packet=p,kernel_statements=ks,checks=dict(basis_function_and_body=True,no_double_count=True),clause_review=[dict(original=c,proof_roots=roots,disposition='Exact original clause retained; SAME-call child substitution, full Result/error/frame/ordered effects in named root; upstream unit provenance remains parent-owned.')for c in cls['caller_domain_obligations']],hypothesis_inventory=inv,admissible_pending_gate=True,review=detail))
assert len(rows)==len({r['row']for r in rows})==30
cs={x['row']:x for x in rows};parents=[]
for c in rows:
 r=by[c['row']]
 for par in b['rows']:
  if par['transaction']!=r['transaction']or r['function']not in par['canonical_callees']:continue
  internal=par['row']in cs
  for kind,required in [('own',c['root_domain'])]+[('inventory:'+o['unit'],o['domain'])for o in r['obligation']['inventory_domain_obligations']]:
   roots=cs[par['row']]['roots']if internal and kind=='own'else None
   clause=dict(id=f'NKC-caller:{par["row"]}:{c["row"]}:{kind}',caller=par['function'],callee=r['function'],required=required,status='DISCHARGED'if roots else'OPEN',discharged_by=roots,reason='SAME internal invocation domain established by composed root.'if roots else'Upstream unit/provenance domain remains caller-owned; helper closure does not close parent.')
   parents.append(dict(parent=par['row'],helper=c['row'],kind=kind,caller_clause=clause,parent_candidate=internal))
put('NKC_CANDIDATE_REVIEW.json',dict(status='PENDING_RAW_GATE',rows=rows,no_double_count=True,comparison_basis='NJW; no candidate baseline delta reused'))
put('NKC_PARENT_CLAUSES.json',dict(status='EXACT_OWN_DOMAINS_AND_UNIT_CONTEXT_RECORDED',clauses=parents,parents=sorted({x['parent']for x in parents}),no_unsubmitted_parent_promotion=True))
(E/'NKC_HYPOTHESIS_INVENTORY.md').write_text('# NKC root hypothesis inventory\n\nComplete kernel statements and owners: NKC_KERNEL_STATEMENTS.json.xz. Every new row retains original hypotheses, unit and caller clauses in NKC_CANDIDATE_REVIEW.json. Exact cuts are reviewed native transcriptions under(aq)(2), not new game assumptions. No arbitrary Ops, endpoint/success/Run premise admitted.\n\n'+''.join(f'- {r["row"]}: {r["hypothesis_inventory"]}. {r["review"]}\n\n'for r in rows))
names=list(dict.fromkeys(n for r in rows for n in r['roots']))
defs=['NJV_CallerBounds.from_count','NJY_Checkpoint.Cut','NJY_Master.Cut','NJY_Entry.Cut','NJY_Registry.Cut']
(E/'NKC_HypothesisReview.lean').write_text('import NKC_COMBINED_IMPORT\nset_option pp.all true\n'+''.join('#print '+n+'\n#print axioms '+n+'\n'for n in names)+''.join('#print '+n+'\n'for n in defs))
print(json.dumps(dict(stage='review',candidates=len(rows),parent_clauses=len(parents),predecessor_roots_unchanged=len(old))))
