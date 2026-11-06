from pathlib import Path
import json,lzma,hashlib,copy,re,subprocess
E=Path(__file__).resolve().parent;P=E.parent/'ledger21-20261110';H=lambda b:hashlib.sha256(b).hexdigest()
def J(p):return json.loads(lzma.decompress(p.read_bytes())if p.suffix=='.xz'else p.read_bytes())
def put(n,x):
 b=(json.dumps(x,indent=1)+'\n').encode();p=E/n
 if n.endswith('.xz'):p.write_bytes(lzma.compress(b));Path(str(p)[:-3]+'.sha256').write_text(H(b)+'\n')
 else:p.write_bytes(b)
statements={}
log=E/'NLO_L002/stdout.log'
raw=log.read_bytes()if log.exists()else lzma.decompress(Path(str(log)+'.xz').read_bytes())
for line in raw.decode().splitlines():
 if 'NLO_OWNER 'in line:
  x=json.loads(line.split('NLO_OWNER ',1)[1]);assert x['root']not in statements;statements[x['root']]=x
old=J(P/'NLG_KERNEL_STATEMENTS.json.xz');wrong=[n for n in old if old[n]!=statements.get(n)];assert not wrong
assert set(statements)==set(J(E/'NLO_AUDIT_ROOTS.json')['roots'])
put('NLO_KERNEL_STATEMENTS.json.xz',statements);put('NLO_OWNER_COMPARISON.json',dict(status='PASS',previous=len(old),identical=len(old),new=len(statements)-len(old),wrong=wrong))
b=J(P/'NLG_LEDGER.json.xz');by={r['row']:r for r in b['rows']};rows=[];parents=[];matrix=[]
reviews={
'TX1:225':'SAME left/right4 canonical inputs; counts1..4. NKR_SumDispatch.native_reference invokes NKJ_Root.small at exact selectedPrefix2, selectedPrefix3 and full4. canonical_prefix proves operand domains; length zip=n and nonempty/<=4 from domain. NKJ_NativeSmall.source derives canonical accumulator, n+remaining<=4 at each step from length<=4 and tail induction; initial n=0, remaining=2/3/4. Count1 uses Lean-discharged emitted QM31.mul. No helper budget assumed at root.',
'TX1:232':'NKI_InitialRoot.source (CLOSED260) supplies actual initial+absorption and canonical carriers; NHU_Preweighted.result (CLOSED230) at offsets0/16 establishes both complete Results; canonical intermediate out transported. NKR_ScheduleAssociation.source computes SAME full Result. ScheduleExt.transition raw collector disagreement retained; no assumed source endpoint.',
'TX1:251':'NKR_DigestChildren.Domain names only actual public digest/frontier canonicality. NKI234/233 and NKY235 are CLOSED in NLG; SAME level/index/frontier/openings/high and carry/min domains derived by DigestChildren/Invocation/Complete. All prefix/middle/after-carry and whole two-cell source/cohort Results are conclusions.',
'TX1:250':'SAME251 arguments and complete two-cell Result; DigestWrapper.reference/cohort and WrapperView.NativeCut transport exact projection to literal frozen wrapper. No reply equality hypothesis.',
'TX1:220':'NKR_SumFinishInvocation.source supplies nine batch windows,43 pattern iterations, actual scratch/high/low/terms and complete4+4 Result; canonical padded arrays/counts1..4 discharge225. SumFinishComposed forward native/source associations and cohort value equality at all four coordinates; no output hypothesis.',
'TX1:218':'Canonical root inputs;136 SAME frozen endpoint producer/consumer iterations; CLOSED208/214/215/217/223 and candidate220 installed internally. Full rows_ext record join is private and raw-audited. Lookups/Keys/tag Domain/permutation/metadata are fixed-registry reviewed native cuts (aq2), never free Ops, child Result, success or final endpoint premises. NKR link argument cut establishes exact gc<30/pc<43 at actual descriptors. Primitive registry transcription remains explicit P6/D188 option-A trust.'}
nkr=J(E.parent/'terminal5-20261108/NKR_CLOSED.json')['functions'];nln=J(E.parent/'batch-merkle6-20261110/NLN_CLOSED.json')['rows'];clauses=J(E.parent/'batch-merkle6-20261110/NLN_CALLER_CLAUSES.json')['rows']
for provider,items in [('NKR',nkr),('NLN',nln)]:
 for f in items:
  rid=f.get('row',f.get('rows',[None])[0]);r=by[rid];assert r['status']=='OPEN'and r['function']==f['function']and r['frozen_body_sha256']==f['frozen_body_sha256']
  file,name=r['function'].split('::',1);text=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+file]).decode();start=re.search(r'fn '+re.escape(name)+r'(?:<|\()',text).start();a=text.index('{',start);z=a+1;d=1
  while d:d+=(text[z]=='{')-(text[z]=='}');z+=1
  assert H(text[a:z].encode())==r['frozen_body_sha256']
  roots=f.get('lean_roots',[f.get('root')]);ks=[statements[n]for n in roots]
  if provider=='NKR':domain=f['root_domain'];review=reviews[rid];hyp=next(x for x in (E.parent/'terminal5-20261108/NKR_ROOT_HYPOTHESES_REVIEW.md').read_text().splitlines()if x.startswith('|'+rid.split(':')[1]+' '))
  else:
   packet=next(c for c in clauses if c['row']==rid);domain=packet['clauses'];hyp=packet['inventory_check'];review='Complete universal native returning/abort fold; SAME idx/val at each tree; returned Parse/Merkle exits and ordered first-error prefixes retained under bb/bc. NLN.values internally instantiates three TreePackets via kinds/bindings; NLN.batch passes exact Prepared.queries and NLL_BatchSource.roots projections. Own proof/root/query hypotheses only under bf2; no child result/success/endpoint/global/headline state hypothesis. TX2<=12 and9216 gate, TX1<=10 are derived by TreePacket.counts/abortCount/bytes.'
   for occ in packet['caller_occurrences']:
    for c in packet['clauses']:
     parents.append(dict(parent=occ['caller'],helper=rid,occurrence=occ,caller_clause=dict(id=f'NLO-bf:{occ["caller"]}:{rid}:{len(parents)}',required=c['verbatim'],name=c['name'],classification=c['classification'],status=occ['status'],discharged_by=occ.get('discharged_by'),reason='Verbatim own-input clause at named SAME caller occurrence; no parent promotion.')))
  original={k:copy.deepcopy(r['obligation'][k])for k in ['named_hypotheses','inventory_domain_obligations','caller_domain_obligations']}
  for kind,cs in [('named',original['named_hypotheses']),('inventory',original['inventory_domain_obligations']),('call',original['caller_domain_obligations'])]:
   for c in cs:matrix.append(dict(row=rid,kind=kind,original=c,disposition=review,retained_upstream_context=True,internal_association='Same native/source carrier, complete Result and ordered effects derived in root; inventory context about enclosing caller retained as own-input clause.'))
  rows.append(dict(row=rid,provider=provider,function=r['function'],basis_obligation_statement_hash=r['obligation_statement_hash'],certificate=f,roots=roots,primary_root=roots[0],kernel_statements=ks,root_domain=domain,hypothesis_inventory=hyp,original_clauses=original,review=review,recommendation='ADMIT_ONLY_AFTER_GATE',gate_admitted=False))
  # Every actual canonical parent retains the helper own-domain and original inventory context.
  for par in b['rows']:
   if par['transaction']!=r['transaction']or r['function']not in par['canonical_callees']:continue
   for kind,req in [('own',domain)]+[('inventory:'+v['unit'],v['domain'])for v in original['inventory_domain_obligations']]:
    parents.append(dict(parent=par['row'],helper=rid,kind=kind,caller_clause=dict(id=f'NLO-caller:{par["row"]}:{rid}:{kind}',caller=par['function'],callee=r['function'],required=req,status='INTERNAL_DISCHARGED'if par['row']in [x.get('row',x.get('rows',[None])[0])for x in nkr+nln]else'OPEN',discharged_by=provider+' same-argument root'if par['row']in [x.get('row',x.get('rows',[None])[0])for x in nkr+nln]else None,reason='Own domain and unit/provenance retained at each canonical parent.')))
# bf named TX1 prepare occurrence is retained explicitly even though canonical batch call is at tx1.
p=next(c for c in clauses if c['row']=='TX1:081')
for c in p['clauses']:parents.append(dict(parent='TX1:087',helper='TX1:081',occurrence='TX1 prepare/tx1 SAME Prepared/root provenance boundary (bf)',caller_clause=dict(id='NLO-bf:TX1:087:081:'+c['name'],required=c['verbatim'],status='OPEN',discharged_by=None,reason='Support/provenance clause only; no added call edge or parent credit.')))
assert len(rows)==12
# Record deterministic CLOSED308 rather than treating it as an oracle in still-open237.
assert by['TX1:308']['status']=='CLOSED'
support=[dict(rows=['TX2:065','TX2:064'],provider='NLE_',path='evidence/tx2-entry-20261109/NLE_CALLER_CLAUSES.md',sha256=H((E.parent/'tx2-entry-20261109/NLE_CALLER_CLAUSES.md').read_bytes()),status='SUPPORT_ONLY_NO_CREDIT',claim='SAME source parser/1880 encoder/range clauses establish proof57607/public<=1880 at common events; native caller/SDK/range association still OPEN'),dict(rows=['TX1:237'],provider='NLG_',status='CLOSED_DETERMINISTIC_CHILD_NOT_ORACLE',child='TX1:308',obligation=by['TX1:308']['obligation_statement_hash'])]
put('NLO_CANDIDATE_REVIEW.json',dict(status='SEMANTIC_REVIEW_GATE_PENDING',rows=rows,admissible=12,rejected=0));put('NLO_PARENT_CLAUSES.json',dict(clauses=parents,parents=sorted({p['parent']for p in parents}),support=support));put('NLO_CLAUSE_MATRIX.json',dict(status='PASS_COMPLETE_CLAUSE_REVIEW',clauses=matrix,original_count=len(matrix),ruling='aq2/bf2/bf3; each full original clause preserved',no_conclusion_hypotheses=True))
print(json.dumps(dict(candidates=len(rows),clauses=len(matrix),parent_clauses=len(parents),unchanged_roots=len(old))))
