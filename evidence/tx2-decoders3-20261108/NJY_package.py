"""Assemble admitted local candidates only after the concrete combined gates."""
from pathlib import Path
import json,lzma,hashlib,re
E=Path(__file__).resolve().parent;Q=E.parent/'tx2-decoders2-20261108';sha=lambda b:hashlib.sha256(b).hexdigest()
rs=[json.loads(l) for l in(E/'NJY_ATTEMPTS.jsonl').read_text().splitlines()];by={r['attempt']:r for r in rs}
for a in ['NJY_L015','NJY_L016','NJY_L018','NJY_L020','NJY_L009','NJY_L010','NJY_L021','NJY_L022','NJY_L023','NJY_L024']:assert by[a]['exit_status']==0,a
for p in E.glob('NJY_*.lean'):
 h=sha(p.read_bytes());passing=[r for r in rs if r['module']==p.stem and r['exit_status']==0 and h in r['source_hashes'].values()];assert passing,'Uncompiled current module '+p.stem
 t=lzma.decompress((E/passing[-1]['attempt']/'stdout.log.xz').read_bytes()).decode();assert 'sorryAx' not in t
comparison=json.loads((E/'NJY_PREDECESSOR_COMPARISON.json').read_text());assert not comparison['mismatches']
loaded=[json.loads(l) for l in lzma.decompress((E/'NJY_NJY_LOADED_scan.jsonl.xz').read_bytes()).decode().splitlines()];assert all(x['imports_match']and not x['dangling']and not x['duplicate_owners']for x in loaded)
roots=json.loads((E/'NJY_AUDIT_ROOTS.json').read_text())['groups'][0]
raw=lzma.decompress((E/'NJY_L022/stdout.log.xz').read_bytes()).decode();assert 'sorryAx' not in raw
for root in roots:assert root in raw,root
base=E.parent/'ledger16-20261108/NJW_LEDGER.json.xz';baseline=json.loads(lzma.decompress(base.read_bytes()));old={r['row']:r for r in baseline['rows']}
N=lambda n:f'NJY_K{n:03}'
def checkpairs(pairs):
 for p,c in pairs:
  for a,exit in [(p,0),(c,1)]:
   r=by[a];assert r['exit_status']==exit,a
   t=lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode();assert 'CBMC timed out' not in t and ('VERIFICATION:- SUCCESSFUL'if exit==0 else'VERIFICATION:- FAILED')in t,a
spec=[('149','identity',[],[],[]),('152','checkpoint',[(N(n),N(n+1))for n in[33,35,37,39,43,69,71]],[61,62,63,64],['TX2:146']),('153','master',[(N(n),N(n+1))for n in[45,47,49,51,53,55,57,59,73]],[65,66,67,68],['TX2:149','TX2:150','TX2:157']),('201','entry',[(N(n),N(n+1))for n in[9,11,13,15]],[25,26,27,28],['TX2:192','TX2:206']),('203','registry',[(N(n),N(n+1))for n in[17,19,21,23]],[29,30,31,32],['TX2:208'])]
items=[];clauses=[]
for number,name,pairs,fidelity,children in spec:
 row='TX2:'+number;r=old[row];assert r['status']=='OPEN'
 checkpairs(pairs)
 for i,n in enumerate(fidelity):assert by[N(n)]['exit_status']==(0 if i==0 else 1)
 for child in children:assert child=='TX2:149' or old[child]['status']=='CLOSED',child
 inherited=[]
 if number=='149':inherited=[['NJQ_K006','NJQ_K007'],['NJQ_K019','NJQ_K020']]
 if number in ['152','153']:inherited += [['NJQ_K010','NJQ_K011'],['NJQ_K012','NJQ_K013']]
 if number=='153':inherited += [['NJQ_K021','NJQ_K022']]
 for p,c in inherited:
  for a,exit in [(p,0),(c,1)]:assert json.loads((Q/a/'receipt.json').read_text())['exit_status']==exit,a
 item=dict(rows=[row],function=r['function'],status='CLOSED under (ah)',ledger_status='LOCAL_AUDITED_CANDIDATE_PENDING_NEXT_LEDGER_GATE',route='(ah)/(ay)(2)-(4), source-ordered segment contracts, (aq) closed-child instantiation, rule-B induction',root_domain='Every valid shared immutable byte slice, every length/content; exact width guard rejects before any payload read; no accepted-child/canonicality restriction added.',native_pairs=pairs,inherited_native_pairs=inherited,returned_record_fidelity=[N(n)for n in fidelity] if fidelity else ['NJQ_K039','NJQ_K047','NJQ_K056','NJQ_K060'],lean_roots=['NJY_Roots.'+name,'NJQ_'+name.title()+'.source','NJQ_Canonical.'+name+'_result'],model_theorem='NJY_Roots.'+name,canonical_installation='NJY_Install.actual_slots directly31/32; raw helper carrier transports to wrapper consumers48/49, whose ProgramError/Box joins are outside this job; digest/error43/44 and wrapper slots48/49 preserved',reviewed_transcription='NJY-RT'+number,complete_result=True,complete_carrier=True,premise_policy='Only input data/local output/log and reviewed native source Cut under (ai)(5)/(aq)(2); identity reference=model root has no Prop input. No free Ops, runtime Boolean, successful-child or endpoint premise.',callee_discharge=children,inventory_unit_context='Original U04 clauses retained; ownership/PDA/active-at-slot remain obligations of actual parents, not guarantees of pure byte decoders.',frozen_body_sha256=r['frozen_body_sha256'],obligation_statement_hash=r['obligation_statement_hash'],effects='Shared immutable input preserved, exact local constructor/iterator buffers, full error Results and no suffix after rejection; no syscall, field product, account mutation or allocation trust added.',audit=['NJY_L020','NJY_L021','NJY_L022','NJY_L023','NJY_L024'],trust='P6/D188 option A RECLASSIFICATION via ReviewedTranscription; no runtime/cryptographic trust row added or removed')
 items.append(item)
 for clause in r['obligation']['caller_domain_obligations']:
  call=clause.get('call',{});namecall=call.get('name','');targets=call.get('targets',[])
  if targets:law='SAME-call CLOSED child full Result and domain instantiated internally; native source segments keep exact arguments/forwarding'
  elif namecall=='any':law='NJQ rule-3 pure byte Iterator.any one-step differential and finite induction; exact source window; no free root reply'
  elif namecall in ['iter_mut','enumerate','next','iter']:law='Pinned P7 / NJQ IterMut rule-3 exclusive lens; native one-step and NJQ finite induction/frame'
  elif namecall in ['try_into','unwrap','from_le_bytes']:law='Executed inside exact native source segment under KMX; every window/cast/unwrap bound proved in NJQ_Read / parser source / NJY_WindowStep'
  elif namecall=='map_err':law='Complete Result mapping segment and NJQ_ChildTotal / NJQ_DigestPort, every error retained'
  else:law='Scalar/constructor operation executed in native source segment; same typed constructor/guard in NJQ reference=model law; no new trust row'
  clauses.append(dict(row=row,id=clause['id'],call=call,classification=law,discharged_by=item['lean_roots'],native_pairs=pairs,inherited_pairs=inherited))
(E/'NJY_CLOSED.json').write_text(json.dumps(dict(schema_version=1,frozen_revision=baseline['frozen_revision'],headline='AspisR1.RPx_Deployed.deployed',functions=items,security_target_established=False,authoritative_count_unchanged=True),indent=1)+'\n')
(E/'NJY_CALLER_CLAUSES.json').write_text(json.dumps(dict(clauses=clauses,count=len(clauses),original_clauses_retained=True,unit_context_retained=True),indent=1)+'\n')
(E/'NJY_LEDGER_DELTA.json').write_text(json.dumps(dict(baseline=str(base.relative_to(E.parent.parent)),baseline_archive_sha256=sha(base.read_bytes()),baseline_counts=dict(CLOSED=484,QUALIFIED=0,OPEN=115,total=599),proposed_rows=[r['row']for r in [old['TX2:'+s[0]]for s in spec]],proposed_occurrence_delta=5,proposed_counts_only_after_next_lead_gate=dict(CLOSED=489,QUALIFIED=0,OPEN=110,total=599),current_authoritative_counts_unchanged=True,body_and_obligation_hashes_preserved=[dict(row=i['rows'][0],frozen_body_sha256=i['frozen_body_sha256'],obligation_statement_hash=i['obligation_statement_hash'])for i in items],no_parent_promoted=True,reviewed_transcription='NJY_REVIEWED_TRANSCRIPTIONS.json',trust_added=[],trust_removed=[]),indent=1)+'\n')
(E/'NJY_AUDIT.json').write_text(json.dumps(dict(gate='PASS_LOCAL_PACKET_PENDING_NEXT_LEDGER_GATE',combined_import=dict(attempt='NJY_L020',exit=0,root='AspisR1.RPx_Deployed.deployed',completed_full_combined_audits=2),raw_ax2=dict(attempt='NJY_L022',exit=0,roots=len(roots),standard_axioms=['propext','Classical.choice','Quot.sound'],same_binary_fixtures='NJY_L021',baseline_NJW_audit_reused=True),NFX=dict(attempt='NJY_L023',exit=0,modules=len(loaded),dangling=0,conflicting_owners=0,import_mismatches=0),pins=dict(attempt='NJY_L024',predecessor_files=comparison['previous_files'],mismatches=0),candidates=5,target_not_yet_established=True,excluded_failures=['NJY_K041 TIMEOUT','NJY_L006 failed bound proof','NJY_L007 failed rewrite proof','NJY_L017 raw helper/wrapper carrier mismatch; outside-slice installation excluded'],skipped=['NJY_K042'],quarantined=[],suspended=[],native_budget=dict(slots=90,launches=89),formal_scopes=sum(r['kind']!='kani'for r in rs),extractions=0),indent=1)+'\n')
print(json.dumps(dict(candidates=len(items),caller_clauses=len(clauses),NFX_modules=len(loaded),raw_roots=len(roots),ledger_credit='WAIT_NEXT_GATE')))
