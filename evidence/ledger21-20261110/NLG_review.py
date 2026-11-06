from pathlib import Path
import json,lzma,hashlib,copy,re,collections
E=Path(__file__).resolve().parent;P=E.parent/'ledger20-20261109';H=lambda b:hashlib.sha256(b).hexdigest()
def raw(p):return p.read_bytes()if p.exists()else lzma.decompress(Path(str(p)+'.xz').read_bytes())
def J(p):return json.loads(lzma.decompress(p.read_bytes())if p.suffix=='.xz'else raw(p))
def put(n,x):
 b=(json.dumps(x,indent=1)+'\n').encode();p=E/n
 if n.endswith('.xz'):p.write_bytes(lzma.compress(b));Path(str(p)[:-3]+'.sha256').write_text(H(b)+'\n')
 else:p.write_bytes(b)
assert J(E/'NLG_SOURCE_REVIEW.json')['status']=='PASS'
b=J(P/'NKW_LEDGER.json.xz');by={r['row']:r for r in b['rows']};statements={}
for l in raw(E/'NLG_L002/stdout.log').decode().splitlines():
 if 'NLG_OWNER 'in l:
  x=json.loads(l.split('NLG_OWNER ',1)[1]);assert x['root']not in statements;statements[x['root']]=x
old=J(P/'NKW_KERNEL_STATEMENTS.json.xz');wrong=[k for k in old if old[k]!=statements.get(k)];assert not wrong
assert set(statements)==set(J(E/'NLG_AUDIT_ROOTS.json')['roots'])
put('NLG_KERNEL_STATEMENTS.json.xz',statements);put('NLG_OWNER_COMPARISON.json',dict(status='PASS',predecessor_roots=len(old),identical=len(old),new_roots=len(statements)-len(old),mismatches=wrong))
domains={'TX2:124':'Variant::S2; SAME original proof length57607; original public length0..1880; arbitrary checkpoint header rejection, checkpoint1768/end1736 derived on entry; SAME Allocator Reservation, every Err/abort prefix', 'TX1:235':'SAME index:anyU64; canonical frontier20x8/opened16/high64; CLOSED234 at EACH actual level/index/array argument; no successful-child or output premise', 'TX2:216':'Every immutable byte slice, every length/content; SAME raw152 call; arbitrary actual Allocator Reservation, full Box carrier, allocator post, heap frame and all Result/abort arms; no allocation-success premise', 'TX2:218':'Every immutable byte slice, every length/content; SAME raw153 call; arbitrary actual Allocator Reservation, full Box carrier, allocator post, heap frame and all Result/abort arms; no allocation-success premise'}
reviews={
'TX2:124':'One NKU.State receives every chronological bind. Header iterator is created after guards and released before digests; all raw/E/K calls update that same record; query windows8/8/6 and semantic/weights full child Results substitute at SAME backing/cursors. G equality includes the entire Run (Result AND chronological log), clauses are conclusions, SAME Frame.reservation supplies allocation44. End cursor guard and full native Prepared/Accumulator tails preserve every final field; variant-only K045 does not supply Prepared. NJU_ResumeRoot transports the same Result to adopted resumeWithOps. Broader model source equality does not enlarge native input scope; proof/public bounds remain explicit caller clauses.',
'TX1:235':'Literal retained loop body independently compared modulo ONLY coherent namespace/type mapping and explicit child slot. Finite loop port assembled by NKY_LiteralRun/LevelsRoot from CLOSED234 at every level; canonical sums remain in domain. Returned2+2 array Result equality holds for EVERY packet witness; determinism eliminates packet choice. Actual post-loop expression is tuple tail with no return or question mark: ruling(bc)-insensitive. Parent canonical/public/Claims context remains a caller obligation.',
'TX2:216':'Full mapped raw152 Result derived at SAME bytes. sole Box::new action176bytes/align8 occurs only on decoder Ok. SAME arbitrary Reservation consumed there: Err allocates nothing, reservation exhaustion panics, allocator fail/div retain allocation prefix. Returning pointer identity is paired with all six typed field-window families, never used to infer payload. Arbitrary old live typed-cell windows reconstruct actual caller-visible heap inside the SAME Result with actual Box and allocator post. Readonly error frame and no returned ghost requirements on abort retained. Existing Allocator/std/P6 interpretation retained.',
'TX2:218':'Full mapped raw153 Result derived at SAME bytes. sole Box::new action304bytes/align8 occurs only on decoder Ok. SAME arbitrary Reservation consumed there: Err allocates nothing, reservation exhaustion panics, allocator fail/div retain allocation prefix. Returning pointer identity is paired with all fourteen typed field-window families, never used to infer payload. Arbitrary old live typed-cell windows reconstruct actual caller-visible heap inside the SAME Result with actual Box and allocator post. Readonly error frame and no returned ghost requirements on abort retained. Existing Allocator/std/P6 interpretation retained.'}
rows=[]
for folder,pre in [('tx2-resume2-20261109','NKU'),('row-bridges-20261109','NKY')]:
 for f in J(E.parent/folder/(pre+'_CLOSED.json'))['rows']:
  rid=f['row'];r=by[rid];roots=f.get('lean_roots',[f.get('source_root'),f.get('cohort_root'),f.get('child_clauses')]);ks=[statements[n]for n in roots]
  cls={k:copy.deepcopy(r['obligation'][k])for k in ['named_hypotheses','inventory_domain_obligations','caller_domain_obligations']}
  inv=dict(ruling='(aq)(2)',ordinary_inputs=domains[rid],added_game_hypotheses=[],details=pre+'_HYPOTHESES.md; NLG_HypothesisReview complete pp.all statements')
  if pre=='NKU':inv.update(root_prop_hypotheses=[],reviewed_cuts='Actual parent native cuts imported via matched local-record transcriptions; all child clauses are outputs, not root assumptions')
  elif rid=='TX1:235':inv.update(root_prop_hypotheses=['hf canonical frontier','ho canonical openings','hs canonical high'],reviewed_cuts='Native234 at SAME actual level, own canonical domain; universally quantified packet witness in conclusion only')
  else:inv.update(root_prop_hypotheses=['decoder: CLOSED raw152/153 cut at SAME bytes','returned: own native returning field/pointer windows, guarded by entered source allocation arm','frame: own native arbitrary typed pre-existing place/coordinate windows'],reviewed_cuts='Reviewed native cuts under(ai)(5); decoder raw law has total domain and is supplied by NKP/NJQ at SAME bytes; none is child success, endpoint, arbitrary Ops or allocation-success premise')
  rows.append(dict(row=rid,provider=pre,function=r['function'],basis_obligation_statement_hash=r['obligation_statement_hash'],submitted_obligation_statement_hash=f.get('baseline_obligation_statement_hash'),frozen_body_sha256=r['frozen_body_sha256'],certificate=f,root_domain=domains[rid],roots=roots,primary_root=roots[0],kernel_statements=ks,original_clauses=cls,clause_review=[dict(original=c,disposition='Original clause preserved; internally substituted child domain/full Result/ordered post/frame via listed roots. Upstream inventory context remains explicit parent clause; no success or provenance assumed.')for c in cls['caller_domain_obligations']],hypothesis_inventory=inv,review=reviews[rid],recommendation='ADMIT_ONLY_AFTER_GATE',missing_clause=None,gate_admitted=False))
assert len(rows)==4
cs={c['row']:c for c in rows};parents=[]
for c in rows:
 r=by[c['row']]
 for par in b['rows']:
  if par['transaction']!=r['transaction']or r['function']not in par['canonical_callees']:continue
  for kind,req in [('own',c['root_domain'])]+[('inventory:'+o['unit'],o['domain'])for o in r['obligation']['inventory_domain_obligations']]:
   clause=dict(id=f'NLG-caller:{par["row"]}:{c["row"]}:{kind}',caller=par['function'],callee=r['function'],required=req,status='OPEN',discharged_by=None,reason='Explicit upstream input/unit scope; no unsubmitted parent credit.')
   parents.append(dict(parent=par['row'],helper=c['row'],kind=kind,caller_clause=clause,parent_candidate=par['row']in cs))
# Native resume restrictions are recorded on every actual ancestor, with a path, never discharged here.
resume=by['TX2:124'];q=collections.deque([['TX2:124']]);seen=set()
while q:
 path=q.popleft();rid=path[0]
 for par in b['rows']:
  if par['transaction']!='TX2'or by[rid]['function']not in par['canonical_callees']or par['row']in path:continue
  nextpath=[par['row']]+path
  if par['row']in seen:continue
  seen.add(par['row']);q.append(nextpath)
  clause=dict(id=f'NLG-upstream:{par["row"]}:TX2:124:native-input',caller=par['function'],callee=resume['function'],required='At every entered resume site, SAME original proof.length=57607 AND SAME original publicBytes.length<=1880; inherited .S2 and SAME actual Reservation; derive from upstream serialized-public/shape context, not resume equality or child success',status='OPEN',discharged_by=None,reason='Native cut scope is narrower than model equality; explicitly retained upward, not a new game hypothesis',path=nextpath)
  parents.append(dict(parent=par['row'],helper='TX2:124',kind='native-input-upward',caller_clause=clause,parent_candidate=False))
assert 'TX2:065'in seen and 'TX2:213'in seen
put('NLG_CANDIDATE_REVIEW.json',dict(status='SEMANTIC_REVIEW_GATE_PENDING',rows=rows,admissible=4,rejected=0,basis='NKW complete obligations, every clause retained',no_double_count=True))
put('NLG_PARENT_CLAUSES.json',dict(clauses=parents,parents=sorted({x['parent']for x in parents}),native_input_ancestors=sorted(seen),no_unsubmitted_parent_promotion=True))
print(json.dumps(dict(candidates=4,admissible=4,parent_clauses=len(parents),native_input_ancestors=sorted(seen),predecessor_roots_unchanged=len(old))))
