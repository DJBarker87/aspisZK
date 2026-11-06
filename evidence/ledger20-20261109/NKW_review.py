from pathlib import Path
import json,lzma,hashlib,copy
E=Path(__file__).resolve().parent;P=E.parent/'ledger19-20261108'
H=lambda b:hashlib.sha256(b).hexdigest()
def J(p):return json.loads(lzma.decompress(p.read_bytes())if p.suffix=='.xz'else p.read_bytes())
def put(n,x):
 b=(json.dumps(x,indent=1)+'\n').encode();p=E/n
 if n.endswith('.xz'):p.write_bytes(lzma.compress(b));Path(str(p)[:-3]+'.sha256').write_text(H(b)+'\n')
 else:p.write_bytes(b)
assert J(E/'NKW_SOURCE_REVIEW.json')['status']=='PASS'
b=J(P/'NKN_LEDGER.json.xz');by={r['row']:r for r in b['rows']};statements={}
for l in((E/'NKW_L002/stdout.log').read_text()if(E/'NKW_L002/stdout.log').exists()else lzma.decompress((E/'NKW_L002/stdout.log.xz').read_bytes()).decode()).splitlines():
 if 'NKW_OWNER 'in l:
  x=json.loads(l.split('NKW_OWNER ',1)[1]);assert x['root']not in statements;statements[x['root']]=x
old=J(P/'NKN_KERNEL_STATEMENTS.json.xz');wrong=[k for k in old if old[k]!=statements.get(k)];assert not wrong
assert set(statements)==set(J(E/'NKW_AUDIT_ROOTS.json')['roots'])
put('NKW_KERNEL_STATEMENTS.json.xz',statements);put('NKW_OWNER_COMPARISON.json',dict(status='PASS',predecessor_roots=len(old),identical=len(old),new_roots=len(statements)-len(old),mismatches=wrong))
rejections={'TX1:235':'NKI_LevelsComplete.source concludes NKI_LevelsFrame.run=ok out and four decoded equalities to NKI_LevelsCohort.model. It does not conclude the literal full emitted append_levels_packed_selector_tensor Result equals the adopted cohort on SAME index/frontier/openings/high. Missing source-body/loop-to-LevelsFrame and decoded-to-literal Result association, including return/frame; no implication theorem supplied. Child234 may close independently.', 'TX2:216':'NKP_BoxCuts.checkpoint reconstructs every value field/error at SAME bytes, but Reservation is unused and output is an unboxed CC. Missing exact Box::new allocation action/carrier identity, fail/div behavior and allocation/post/cleanup/frame binding for arbitrary reservation in the SAME wrapper invocation. No allocation-success premise may replace it.', 'TX2:218':'NKP_BoxCuts.master reconstructs every value field/error at SAME bytes, but Reservation is unused and output is an unboxed CM. Missing exact Box::new allocation action/carrier identity, fail/div behavior and allocation/post/cleanup/frame binding for arbitrary reservation in the SAME wrapper invocation. No allocation-success premise may replace it.'}
review_text={
'NKM':'K004/005 arbitrary canonical reply parent establishes full three/seven event native trace; K026/028 isolates one assumed-spec boundary on arbitrary canonical operands and every field kind. Not a full constrained-contract pass; K025/K027 TIMEOUT excluded. NKM_NaturalLaws base bounds/tower identities, NKM_SpecLaws and NKM_EmittedMul instantiate reached replies in Lean via NKM_FieldLaws. Trace.complete/OuterTrace.complete/error_order preserve SingularParameter before subfield rejection. Canonicality/roundtrip and fallback inverse certificates are proved; no large kernel reduction. This is the same full Result/effects obligation under(y)(3)/(aq)(5), not weaker success-only G.',
'NKI':'Actual frozen native cuts with field rule-A laws; complete returned records and original child arguments, canonical domains, frames and loop inductions. NJX children are CLOSED in NKN. Domain and source/model association inspected in named root and its imported packet definitions. 235 decoded model is separately rejected until complete literal Result bridge is supplied.',
'NKL':'NKL_ScanRoot.deployed/adopted equate complete native cut chain, emitted scanner and MultiproofParserRef.parser_reference.scan at SAME57607 bytes; exact readonly frame and first-rejection prefix/no later event. CLOSED189 child substituted at SAME flag/window with all domains internally derived; canonical_scan is free of the confirmed(bc) post-loop return-loss pattern.',
'NKP':'All6 checkpoint and14 master field-window families and each mapped error are reconstructed from actual returned Box observations. Every21 account and13 Tree error constructor maps to InvalidAccountData. SAME raw152/153 total domains are internal. Byte-uniformity removes 0..33 harness extent restriction. These observations establish complete value/error support, but do not supply arbitrary allocation outcome/effect/identity; row remains OPEN.'}
rows=[]
for folder,pre in [('circle-points','NKM'),('terminal4','NKI'),('batch-merkle3','NKL'),('tx2-adapters2','NKP')]:
 e=E.parent/(folder+'-20261108');packet=J(e/f'{pre}_CLOSED.json')
 for f in packet['functions']:
  f=dict(f); f.setdefault('rows',[f.get('row')]); f.setdefault('lean_roots',f.get('roots',[f.get('model_theorem')])); f.setdefault('root_domain',f.get('domain','SAME original57607-byte proof; every scanner prefix'))
  for rid in f['rows']:
   r=by[rid];assert r['status']=='OPEN'and r['function']==f['function'];assert pre=='NKI' or f.get('frozen_body_sha256',r['frozen_body_sha256'])==r['frozen_body_sha256']
   hs=f.get('baseline_obligation_statement_hash',f.get('obligation_statement_hash'))
   ks=[statements[n]for n in f['lean_roots']];cls={k:copy.deepcopy(r['obligation'][k])for k in ['named_hypotheses','inventory_domain_obligations','caller_domain_obligations']}
   rows.append(dict(row=rid,provider=pre,function=r['function'],basis_obligation_statement_hash=r['obligation_statement_hash'],submitted_obligation_statement_hash=hs,submitted_hash_matches_current_basis=hs==r['obligation_statement_hash']if hs else None,frozen_body_sha256=r['frozen_body_sha256'],certificate=f,root_domain=f.get('root_domain','SAME immutable byte slice, all lengths/contents, arbitrary Reservation'),roots=f['lean_roots'],primary_root=f['lean_roots'][0],kernel_statements=ks,original_clauses=cls,clause_review=[dict(original=c,disposition='Retained verbatim. SAME reached child args/domain/full Result/frame in named roots; parent unit context remains incoming.'if rid not in rejections else 'NOT DISCHARGED: '+rejections[rid])for c in cls['caller_domain_obligations']],hypothesis_inventory=dict(allowed_ruling='(aq)(2)',ordinary_inputs=f.get('root_domain'),native_cuts='Reviewed parent local-record cuts under(ai)(5), existing CLOSED children at SAME arguments; no child-success or endpoint premise retained as root hypothesis',added_game_hypotheses=[],details=pre+'_HYPOTHESES; NKW_HypothesisReview prints full positive roots'),review=review_text[pre],recommendation='KEEP_OPEN'if rid in rejections else'ADMIT_ONLY_AFTER_GATE',missing_clause=rejections.get(rid),gate_admitted=False))
assert len(rows)==10 and len({r['row']for r in rows})==10
cs={c['row']:c for c in rows};parents=[]
for c in rows:
 r=by[c['row']]
 for par in b['rows']:
  if par['transaction']!=r['transaction']or r['function']not in par['canonical_callees']:continue
  for kind,req in [('own',c['root_domain'])]+[('inventory:'+o['unit'],o['domain'])for o in r['obligation']['inventory_domain_obligations']]:
   discharged=par['row']in cs and kind=='own'and par['row']not in rejections and c['row']not in rejections
   clause=dict(id=f'NKW-caller:{par["row"]}:{c["row"]}:{kind}',caller=par['function'],callee=r['function'],required=req,status='DISCHARGED'if discharged else'OPEN',discharged_by=cs[par['row']]['roots']if discharged else None,reason='SAME concrete child arguments and domain derived internally.'if discharged else 'Own domain and upstream unit/provenance remain explicit parent obligations; no unsubmitted parent credit.')
   parents.append(dict(parent=par['row'],helper=c['row'],kind=kind,caller_clause=clause,parent_candidate=par['row']in cs))
put('NKW_CANDIDATE_REVIEW.json',dict(status='SEMANTIC_REVIEW_GATE_PENDING',rows=rows,admissible=7,rejected=3,no_double_count=True,basis='NKN complete clauses retained, not candidate local headline counts'))
put('NKW_PARENT_CLAUSES.json',dict(clauses=parents,parents=sorted({x['parent']for x in parents}),no_unsubmitted_parent_promotion=True))
print(json.dumps(dict(candidates=10,admissible=7,kept_open=3,parent_clauses=len(parents),predecessor_roots_unchanged=len(old))))
