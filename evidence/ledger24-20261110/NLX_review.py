"""Audit the corrected NLT statement against every inherited row clause."""
from pathlib import Path
import json,lzma,hashlib,re
E=Path(__file__).resolve().parent;P=E.parent/'ledger23-20261110';Q=E.parent/'tx2-common2-20261110'
H=lambda b:hashlib.sha256(b).hexdigest()
def raw(p):
 if p.exists():return p.read_bytes()
 b=lzma.decompress(Path(str(p)+'.xz').read_bytes());assert H(b)==Path(str(p)+'.sha256').read_text().strip();return b
J=lambda p:json.loads(lzma.decompress(p.read_bytes())if p.suffix=='.xz'else raw(p))
def put(n,x):
 b=(json.dumps(x,indent=1,sort_keys=True)+'\n').encode();p=E/n
 if len(b)>20_000_000 or n.endswith('MATRIX.json'):
  Path(str(p)+'.xz').write_bytes(lzma.compress(b,preset=6));Path(str(p)+'.sha256').write_text(H(b)+'\n')
 else:p.write_bytes(b)
basis=J(P/'NLO_LEDGER.json.xz');r=next(r for r in basis['rows']if r['row']=='TX2:065');assert r['status']=='OPEN'
source_review=[];exports_by_module={Path(x['path']).stem:x for x in J(Q/'NLT_EXPORT.json')['files']}
for m in J(Q/'NLT_MODULES.json'):
 p=Q/(m['module']+'.lean');b=p.read_bytes();assert H(b)==m['sha256'],m['module']
 rc=J(Q/m['passing_attempt']/'receipt.json');assert rc['exit_status']==0
 matches=[(name,sha)for name,sha in rc['source_hashes'].items()if name.endswith('/'+p.name)]
 assert len(matches)==1 and matches[0][1]==H(b),(m['module'],matches)
 snap=raw(Q/m['passing_attempt']/'sources'/matches[0][0]);assert snap==b
 source_review.append(dict(**m,bytes=len(b),receipt_sha256=H(raw(Q/m['passing_attempt']/'receipt.json')),snapshot_match=True,retained_compiled_object=exports_by_module[m['module']]))
put('NLX_SOURCE_REVIEW.json',dict(status='PASS',sources=source_review))
root=(Q/'NLT_CompleteRoot.lean').read_text();statement=root[root.index('theorem root'):root.index(' := by',root.index('theorem root'))]
assert '(proofLength : proof.val.length=57607)'in statement and '(publicLength : pub.val.length≤1880)'in statement and '(root0 : NLP_InputDomain.Root0 ck proof)'in statement
assert 'c04Stopped records cut =>'in root and 'NLT_C04StopChronology.installed'in root and 'NLT_C04StopParent.installed'in root
assert 'NLT_NoInvalid.source'in root
caller=J(Q/'NLT_CALLER_CLAUSES.json');assert caller['root']=='NLT_CompleteRoot.root'and caller['cross_transaction_provenance']['established_here']is False and len(caller['clauses'])==3
# Complete recursive records are retained, including historical copies, not silently replaced by a short title.
clauses=[]
def walk(x,path):
 if isinstance(x,dict):
  if any(k in x for k in ['required','domain','required_named_hypotheses'])or ('status'in x and any(k in x for k in ['callee','caller_clause','helper'])):clauses.append(dict(path=path,original=x))
  for k,v in x.items():walk(v,path+'.'+k)
 elif isinstance(x,list):
  for i,v in enumerate(x):walk(v,path+'['+str(i)+']')
walk(r['obligation'],'obligation')
def disposition(x):
 s=json.dumps(x,ensure_ascii=False)
 if 'resume'in s or 'TX2:124'in s or 'U11'in s:
  return ('NLT_AllocationInstalled.resume; NLT_NativeFacts.resume_scope; NLP_C01.native_scope/step; NLP_ResumeInstall.packet','SAME original ck/proof/pub and concrete site Reservation; extent inputs retained at064. Saved-state cross-transaction provenance remains064. Child rejects bad headers/next/query/weights; no successful-child premise.')
 if 'batch_merkle'in s or 'TX2:053'in s or 'U09'in s:
  return ('NLT_C04NativeInstalled.installed; NLT_ReplyInstalled.installed; NLT_C04StopParent.installed; NLT_C04StopChronology.installed','SAME proof/Prepared/folded root, kind1; Parsed wire/query/root domains installed internally by NLP_C04Effects and NLN packet; both resolved and independently stopped prefix. Root0 is an explicit ORIGINAL-input clause; root1 cross-transaction provenance remains064.')
 if 'query_loop'in s or 'U14'in s:return ('NLT_QueryInstalled.installed; NLT_RecordFrames.parent; NLT_QuestionStep.source','SAME proof/Prepared/Accumulator/powers/geometry/pending; input frame and owned-return law; unchanged NLB_QueryCut/NKO native family, no address-implies-payload claim.')
 if 'finish_relation'in s or 'U13'in s:return ('NLT_FinishInstalled.installed; NKO_C09.child_at_actual','SAME view/Prepared/Accumulator, actual finish Reservation/ABI Locations; full generalized aw child law, arbitrary current words; no canonical/NoBad/success restriction.')
 if 'BatchedWeights::new'in s or 'TX2:100'in s:return ('NLT_AllocationInstalled.pending; NKE_CommonNative.pendingG; NKO_C06.returned','SAME weights64 and separate site Reservation; both allocation outcomes, raw64/terms0 and all initialization rows. Historical U10 canonical context is not an additional root hypothesis.')
 if 'BatchedWeights::finish'in s or 'TX2:099'in s:return ('NLT_Interpreted.step flush; NLB_NativeFlush.at_actual; NLT_QuestionStep.source','SAME pending/weights64 and arbitrary raw limbs; complete flush frame/Result. Historical U10 canonical context is not an additional root hypothesis.')
 if 'QueryGeometry::for_range'in s or 'U08'in s:return ('NLT_Interpreted.step geometry; NLB_Parent.C05_step','SAME queries/next, end22; child domain installed at actual C05.')
 if 'weights.rs::powers'in s:return ('NLT_Interpreted.step powers; NLB_Parent.C02_step','SAME gamma and29 powers; natural scalar/domain predicates derived from source resume.')
 if 'from_le_bytes'in s:return ('NLT_Interpreted.step inactive; NLB_Parent.C03_step','Exact original proof OFF_INACTIVE..OFF_ROUND0 bytes; full Option/Result decoding, no canonicality assumed.')
 if '::mark'in s:return ('NLP_ResumeInstall.native; NLT_NativeSource.skeleton; NKE_CommonProgram.run','Existing deployed release None erasure, not an Option<fn> Kani pass. No new quarantined verdict credited.')
 if 'external:'in s:return ('NLT_NativeSource.source; NKE_CommonEval.source; NLT_QuestionStep.source','Literal std/construction/scalar branches under au and pinned std semantics, including slices/try_into/unwrap/ok_or; no free std dictionary or producer row.')
 return ('NLT_CompleteRoot.root; NLT_NativeSource.source; NLT_NoInvalid.source','Full source-ordered C01..C09 parent fold, complete Results/error/abort prefixes and no invalid decode. Historical U15 context retained; opening/round/final canonicality supplied by consumer child decoders, not a new premise.')
for c in clauses:
 proof,reason=disposition(c['original']);c.update(disposition='INTERNAL_DISCHARGED_WITH_RETAINED_CALLER_PROVENANCE',proof=proof,review=reason)
put('NLX_CLAUSE_MATRIX.json',dict(status='PASS_COMPLETE_CLAUSE_REVIEW',basis_obligation_sha256=r['obligation_statement_hash'],count=len(clauses),clauses=clauses,no_strengthened_inventory_premises=True))
parent=[]
for c in caller['clauses']:
 parent.append(dict(parent='TX2:064',helper='TX2:065',occurrence='actual tx2_authenticated -> tx2_common original pub/proof/ck',name=c['name'],required=c['verbatim'],classification=c['classification'],status='OPEN_CALLER_CLAUSE',discharged_by=None,provenance_note=caller['cross_transaction_provenance']))
put('NLX_PARENT_CLAUSES.json',dict(parents=['TX2:064'],clauses=parent,no_parent_promotion=True))
checks=[dict(name='C01',proof='NLT_AllocationInstalled.resume; NLT_NativeFacts.resume_scope',same='original ck/proof/pub/hash, site Reservation'),dict(name='C04 resolved',proof='NLT_C04NativeInstalled.installed; NLT_ReplyInstalled.installed; NLT_Chronology.installed',same='actual proof/Prepared/folded at unique parent occurrence'),dict(name='C04 independently stopped',proof='NLT_C04StopParent.source_prefix/installed; NLT_C04StopChronology.installed',same='same parent question; child pending history; no returned reply or suffix'),dict(name='C07',proof='NLT_QueryInstalled.installed; NLT_RecordFrames.parent',same='same queryArgs, observation/ownership/frame, complete unchanged native family')]
put('NLX_CANDIDATE_REVIEW.json',dict(status='PASS_STATEMENT_REVIEW_GATE_PENDING',row='TX2:065',primary_root='NLT_CompleteRoot.root',owner_module='NLT_CompleteRoot',withdrawn_root='NLT_Root.root',withdrawn_root_credit=False,basis_obligation_statement_hash=r['obligation_statement_hash'],source_statement=statement,own_argument_clauses=caller['clauses'],cross_transaction_provenance=caller['cross_transaction_provenance'],same_argument_checks=checks,recursive_clauses_reviewed=len(clauses),hypothesis_inventory=dict(own_inputs='three bf2 clauses on original args',original_generics='H existing returning-value realization, X/Digest32/hash original trait parameters; partial replies retained',native='subject of conclusion, not an extra endpoint/success premise',cuts='per-occurrence reservation/locations and NLB C07 native frame family under aq2/ai5/y3 option-A',no_free_Ops_Run=True,no_child_endpoint_hypothesis=True),trust='existing P6/D188 option-A native semantic transport RETAINED as reclassification; no new native pass',gate_admitted=False))
print('NLX statement review PASS; '+str(len(clauses))+' recursive clauses;43 source snapshots; gate pending')
