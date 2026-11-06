from pathlib import Path
import json,lzma,hashlib,copy,re
E=Path(__file__).resolve().parent;P=E.parent/'ledger15-20261108'
H=lambda b:hashlib.sha256(b).hexdigest()
def J(p):return json.loads(lzma.decompress(p.read_bytes())if p.suffix=='.xz'else p.read_bytes())
def put(n,x):
 raw=(json.dumps(x,indent=1)+'\n').encode();p=E/n
 if n.endswith('.xz'):
  p.write_bytes(lzma.compress(raw));Path(str(p)[:-3]+'.sha256').write_text(H(raw)+'\n')
 else:p.write_bytes(raw)
b=J(P/'NJO_LEDGER.json.xz');by={r['row']:r for r in b['rows']}
q=E/'NJW_L002/stdout.log';lines=(q.read_text() if q.exists() else lzma.decompress(Path(str(q)+'.xz').read_bytes()).decode()).splitlines();statements={}
for l in lines:
 if 'NJW_OWNER 'in l:
  x=json.loads(l.split('NJW_OWNER ',1)[1]);assert x['root']not in statements;statements[x['root']]=x
assert len(statements)==len(J(E/'NJW_AUDIT_ROOTS.json')['roots'])
old=J(P/'NJO_KERNEL_STATEMENTS.json.xz');wrong=[r for r in old if old[r]!=statements.get(r)];assert not wrong,wrong[:5]
put('NJW_KERNEL_STATEMENTS.json.xz',statements)
put('NJW_OWNER_COMPARISON.json',dict(status='PASS',predecessor_roots=len(old),identical=len(old),new_roots=len(statements)-len(old),mismatches=wrong,canonical_owners_preserved=['NGK','NIU','NJB','NIX','NJO']))
specs=J(E/'NJW_SPECS.json')[1:];packets={p['row']:p for p in J(E.parent/'multiproof3-20261108/NJP_ROW_PACKETS.json')};rows=[]
for folder,pre in specs:
 for f in J(E.parent/folder/f'{pre}_CLOSED.json')['functions']:
  for rid in f['rows']:
   r=by[rid];assert r['status']=='OPEN'and r['function']==f['function']
   if f.get('frozen_body_sha256'):assert r['frozen_body_sha256']==f['frozen_body_sha256']
   if f.get('obligation_statement_hash'):assert r['obligation_statement_hash']==f['obligation_statement_hash']
   p=packets.get(rid)
   if p:
    orig=p['original_inventory'];assert orig['frozen_body_sha256']==r['frozen_body_sha256']
    assert orig['obligation']==r['obligation'],rid
    assert len(p['caller_clauses'])==len(r['obligation']['caller_domain_obligations'])
    for original,reviewed in zip(r['obligation']['caller_domain_obligations'],p['caller_clauses']):
     for k,v in original.items():
      if k not in ['status','discharged_by','owner_packets']:assert reviewed[k]==v,(rid,k)
   inv=dict(root_inputs=f['root_domain'],headline_hypotheses=[],reviewed_parent_cuts=[],retained_caller_input_domains=[],extra_logical_hypotheses=[],endpoint_or_success_premises=[])
   if pre=='NJI':
    inv['reviewed_parent_cuts']={'TX2:150':['NJI_PolicyTotal.Cut: K035/036 scalar length + K025/026 104byte stage; closedReply internally fixed'], 'TX2:157':['NJI_MasterCut.Cut: K023/024; exact closed policy reply and source any callback internally fixed; K031/032 iteration'],'TX2:206':[],'TX2:208':[]}[rid]
    detail=f['callee_discharge']+' Emitted-body identity is independently recorded in NJW_NJI_EMISSION.json. All immutable typed inputs/full Result errors retained.'
   elif pre=='NJM':
    inv['reviewed_parent_cuts']=['NJM_RoundsCut.Cut native: EXACT K016–019 (ai)(5) transcription; sole Prop input']if rid=='TX1:134'else[]
    detail='Final InvocationRoots root splits SAME actual Prefix parser internally; Fin10/Fin27 are actual private call positions. Rejection is callee non-entry, not whole-caller closure. Child Results, framed/canonical domains and all error/abort prefixes are derived internally. '+('The sole Prop cut is inventoried (ai)(5), not a new game premise.'if rid=='TX1:134'else'No external parse/child success premise.')
   elif pre=='NJP':
    inv.update(p['aq2_hypothesis_inventory']);inv['reviewed_parent_cuts']=['NJP_ControllerTrace.Cut: native22descriptor control plus NJE per-cell/linear native cuts after SAME child substitution'if rid=='TX1:306'else'NJP_CompressionPacket.CallerCut: actual K057/058/059 SAME seed/first8/input-frame; closed permutation installed at that seed']
    detail=p['aq2_hypothesis_inventory']['detail']+' K057/058/059 supersede stale K010/011/012 labels in the theorem comment; complete KMX coverage is required.'
   else:
    inv['retained_caller_input_domains']=[f['root_domain']]
    inv['reviewed_parent_cuts']=['NJL_EndpointLookup.Cut index consumer: actual K019/020 literal genuine lookup; caller_weight proves SAME link binary domain']if rid=='TX1:214'else[]
    detail=f['premise_policy']+' Complete source/native association table NJL_NATIVE_TO_SOURCE.json reviewed under (aq)(5); canonical input, finite index and binary weight are caller domains, never child output assumptions.'
   ks=[statements[root]for root in f['lean_roots']]
   cls={k:copy.deepcopy(r['obligation'][k])for k in['named_hypotheses','inventory_domain_obligations','caller_domain_obligations']}
   clause_review=[]
   for c in cls['caller_domain_obligations']:
    if pre=='NJP':proved=next(x for x in p['caller_clauses']if x['id']==c['id']);why=proved.get('discharged_by')
    else:why=f['lean_roots']
    clause_review.append(dict(id=c['id'],original=c,proof_roots=why,disposition='SAME internal child domains/complete Result/frame/order instantiated by these roots; conservative alternatives resolved by the typed source. Std constructors, indexing, casts, array operations remain pinned Aeneas/P7 models and actual native cut operations. Original clause retained verbatim.'))
   rows.append(dict(row=rid,provider=pre,function=r['function'],basis_obligation_statement_hash=r['obligation_statement_hash'],frozen_body_sha256=r['frozen_body_sha256'],certificate=f,root_domain=f['root_domain'],roots=f['lean_roots'],primary_root=f.get('model_theorem',f['lean_roots'][-1]),original_clauses=cls,packet=p,kernel_statements=ks,checks=dict(basis_function_and_body=True,original_obligation_hash=f.get('obligation_statement_hash'),njp_original_full_obligation_equal=bool(p),no_double_count=True),clause_review=clause_review,hypothesis_inventory=inv,admissible_pending_gate=True,review=detail))
assert len(rows)==len({r['row']for r in rows})==21
cs={x['row']:x for x in rows};parents=[]
for c in rows:
 r=by[c['row']]
 for par in b['rows']:
  if par['transaction']!=r['transaction']or r['function']not in par['canonical_callees']:continue
  internal=par['row']in cs
  # Propagate the EXACT original unit context and the helper's precise own domain.
  for kind,required in [('own',c['root_domain'])]+[('inventory:'+o['unit'],o['domain'])for o in r['obligation']['inventory_domain_obligations']]:
   roots=cs[par['row']]['roots']if internal and kind=='own'else None
   status='DISCHARGED'if roots else'OPEN'
   clause=dict(id=f'NJW-caller:{par["row"]}:{c["row"]}:{kind}',caller=par['function'],callee=r['function'],required=required,status=status,discharged_by=roots,reason='Internal same-argument callee domain supplied by composed parent roots.'if roots else'Upstream same-source provenance/unit domain retained. Conditional helper closure does not discharge the enclosing caller.')
   parents.append(dict(parent=par['row'],helper=c['row'],kind=kind,caller_clause=clause,parent_candidate=internal))
put('NJW_CANDIDATE_REVIEW.json',dict(status='PENDING_RAW_GATE',rows=rows,no_double_count=True,comparison_basis='NJO, never ledger13/14 counts'))
put('NJW_PARENT_CLAUSES.json',dict(status='EXACT_OWN_DOMAINS_AND_UNIT_CONTEXT_RECORDED',clauses=parents,parents=sorted({x['parent']for x in parents}),no_unsubmitted_parent_promotion=True))
text='# NJW root hypothesis inventory\n\nAll statements are kernel-printed in L002 and retained in NJW_KERNEL_STATEMENTS.json.xz. Standard axioms only still require raw gate. Domains are conditional caller obligations, not new game hypotheses. No arbitrary Ops, child-success, endpoint or Run root premise is admitted.\n\n'
for r in rows:text+=f"- {r['row']} ({r['provider']}), roots {', '.join(r['roots'])}: {r['hypothesis_inventory']}. {r['review']}\n\n"
(E/'NJW_HYPOTHESIS_INVENTORY.md').write_text(text)
# One focused statement/body inventory after raw campaign; no new theorem.
names=list(dict.fromkeys(root for c in rows for root in c['roots']))
defs=['NJI_PolicyTotal.Cut','NJI_PolicyParser.raw','NJI_MasterModel.raw','NJI_MasterCut.Cut','NJI_V1Models.registry','NJI_V1Models.entry','NJI_Extracted.aspis_statement.pool_v1.format.decode_verifier_policy_v1','NJI_Extracted.aspis_statement.pool_v1.pair_forest_accounts.validate_master','NJI_Extracted.aspis_statement.pool_v1.verifier_registry.validate_verifier_registry_entry_v1','NJI_Extracted.aspis_statement.pool_v1.verifier_registry.validate_verifier_registry_v1','AspisR1.NJM_RoundsCut.Cut','NJP_ControllerTrace.Cut','NJP_CompressionPacket.CallerCut','AspisR1.NJL_EndpointLookup.Cut','AspisR1.NJL_EndpointRoot.reference','AspisR1.NJL_TagRoot.reference','AspisR1.NJL_TagMeaning.model']
(E/'NJW_HypothesisReview.lean').write_text('import NJW_COMBINED_IMPORT\nset_option pp.all true\n'+''.join('#print '+n+'\n#print axioms '+n+'\n'for n in names)+''.join('#print '+n+'\n'for n in defs))
print(json.dumps(dict(stage='review',candidates=len(rows),parent_clauses=len(parents),predecessor_roots_unchanged=len(old))))
