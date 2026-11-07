"""Read-only candidate/certificate inspection. No prover invocation."""
from pathlib import Path
import json,lzma,hashlib,subprocess,re,copy
E=Path(__file__).resolve().parent;R=Path.cwd();T=E.parent/'tx1-principal-20261111';Q=E.parent/'tx2-auth-20261111';F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';H=lambda b:hashlib.sha256(b).hexdigest()
def raw(p):
 if p.exists():return p.read_bytes()
 if Path(str(p)+'.xz').exists():
  b=lzma.decompress(Path(str(p)+'.xz').read_bytes());assert H(b)==Path(str(p)+'.sha256').read_text().strip();return b
 rel=str(p.relative_to(R))if p.is_absolute()else str(p)
 z=subprocess.run(['git','show','HEAD:'+rel],capture_output=True)
 if z.returncode==0:return z.stdout
 b=lzma.decompress(subprocess.check_output(['git','show','HEAD:'+rel+'.xz']));assert H(b)==subprocess.check_output(['git','show','HEAD:'+rel+'.sha256'],text=True).strip();return b
def J(p):return json.loads(lzma.decompress(raw(p))if p.suffix==".xz"else raw(p))
def put(n,x):(E/('NNK_'+n+'.json')).write_text(json.dumps(x,indent=1)+'\n')
base=J(E.parent/'ledger26-20261111/NNI_LEDGER.json.xz');by={r['row']:r for r in base['rows']}
lock=H(subprocess.check_output(['git','show',F+':Cargo.lock']))
# Validate inherited native component route using identical checks to ledger26.
pins=dict(lock_before=lock)
s=(E.parent/'ledger26-20261111/NNI_review.py').read_text();snippet=s[s.index("patch=raw("):s.index("review217=dict(")]
exec(compile(snippet,'NNK inherited native checks','exec'))
put('NATIVE_COMPONENTS',dict(runs=runs,inherited=ndb,reference=ref,KMX_sha256=H(patch)))
# Re-run only the local immutable receipt validator, writing exclusively NNK evidence.
s=(E.parent/'tx2-217-controls-20261111/NNJ_validate.py').read_text().replace('E=Path(__file__).resolve().parent',"E=Path('evidence/tx2-217-controls-20261111')").replace("(E/'NNJ_VALIDATION.json')","(Path('evidence/ledger27-20261111')/'NNK_NNJ_VALIDATION.json')")
exec(compile(s,'NNK read-only NNJ validator','exec'),{'__file__':__file__})
# Fresh actual-body emissions: immutable source/lock/LLBC/output pins, receipts and bc spans.
emissions=[]
for folder,prefix,sub,receipt in [('tx1-observed3-20261110','NMP','NMP_emitted/prepare','NMP_E002'),('tx2-auth-20261111','NMX','NMX_registry_r6_emitted','NMX_E006')]:
 d=E.parent/folder;p=J(d/sub/(prefix+'_PINS.json'));rc=J(d/receipt/'receipt.json')
 assert p['frozen_revision']==F and p['charon_exit']==p['aeneas_exit']==rc['exit_status']==0
 assert p['lock_before']==p['lock_after']==lock
 assert p['candidate_sha256']==H(subprocess.check_output(['git','show',F+':crates/aspis-r1-cost-probe/src/candidate.rs']))
 for rel,h in p['outputs'].items():assert H(raw(d/sub/rel))==h,(folder,rel)
 llbc='prepare.llbc'if prefix=='NMP'else'registry.llbc';assert H(raw(d/sub/llbc))==p['llbc_sha256']
 if prefix=='NMP':
  bc=J(d/'NMP_BC_AUDIT.json');assert bc['status']=='PASS_NO_POST_LOOP_PATTERN_IN_OWN_FRESH_BODIES'
  for z in bc['definitions']:assert H(subprocess.check_output(['git','show',F+':'+z['file']]))==z['source_sha256']
 else:
  bc=J(d/'NMX_REGISTRY_SOURCE_AUDIT.json');assert bc['bc']['flagged_exits']==[] and bc['bc']['root']=='no loops'
  assert bc['raw_sha256']==p['outputs']['raw/NMX_registry/Funs.lean']
  assert p['opaque_exclusion_witness']['parent_current_body']=='Opaque'and p['opaque_exclusion_witness']['child_absent']
 emissions.append(dict(folder=folder,receipt=receipt,root=p['root'],pins_sha256=H(raw(d/sub/(prefix+'_PINS.json'))),LLBC_sha256=p['llbc_sha256'],outputs=p['outputs'],bc=bc,source_revision=rc['source_revision'],wall_seconds=rc['wall_seconds'],peak_rss_kib=rc['peak_rss_kib'],swaps=rc['swaps'],opacity=p.get('opacity'),note=p.get('validation_resume')))
put('EMISSION_REVIEW',dict(status='PASS',new_extractions=0,emissions=emissions))
old217=copy.deepcopy(J(E.parent/'ledger26-20261111/NNI_CANDIDATE_REVIEW.json')['candidates'][1]);old217['NNK_superseded_review']=copy.deepcopy(old217['ruling_t_decision']);old217.update(status='STATIC_REVIEW_PASS_GATE_PENDING',gate_admitted=False,exact_blocker=None,remaining_parameters=[],trust_status='ReviewedTranscription-TX2:217 used if gate admits; (ah), option A, addition/reclassification only',ruling_t_decision=dict(sufficient=True,ruling='(br)',decoder=['NNJ_K001 intended caller FAIL','NNJ_K002 real PASS','NNJ_K003 contract PASS','NNJ_K004 modifies FAIL','NNJ_K005 inverted FAIL'],assignment=['NNJ_K006 contract PASS','NNJ_K007 inverted FAIL','NNJ_K010 modifies FAIL'],assignment_stub_verified_use=False,composition='proof_for_contract plus Lean only; actual frozen assignment K015/K016',uncredited=['NNJ_K009','NNJ_K012','NNJ_K015'],notes='NNJ_CONTROLS K005 shape label says assignment but its harness and failed postcondition are the actual decoder shape; corrected reporting here. Decoder constructor bound <=1 BorshIoError payload is a calibration bound only, never a row domain. No native arbitrary full-String result havoc relied on.'))
old217['additional_shape_obligations']=[dict(status='NOT_REQUIRED_BY_BR',prior=old217['additional_shape_obligations'],reason='assignment never substituted via stub_verified; positive, inverted ensures and modifies controls verified')]
reviews=[]
for row,name,owner,statement,producer,chain,own in [
 ('TX1:137','AspisR1.NNG_Candidate137.candidate','NNG_Candidate137','RSL.TX1_137.RowSpec_137 LIB_VLib.library NNG_Producer137.producer','AspisR1.NNG_Producer137.producer',['NNG_Erasure137.source','NNG_Producer137.tree','NNG_SourceParse137.source','NNG_SourcePublic137.source','NNG_SourceBegin137.source','NNG_FinishOccurrence137.observation','NNG_FinishOccurrence137.occurrence'],['LIB_VLib.library.publicDom a.public_','LIB_VLib.library.semanticBytesDom a.bytes (length <= 57607)']),
 ('TX1:087','AspisR1.NNG_Candidate087.candidate','NNG_Candidate087','RSL.TX1_087.RowSpec_087 LIB_Instances.VL LIB_Instances.P NNG_Producer087.producer','AspisR1.NNG_Producer087.producer',['NNG_Producer087.source','NNG_Producer087.tree','NNG_SourceFront087.source','NNG_ReadyFront087.returned','NNG_PreparedOccurrence087.input_exact','NNG_PreparedOccurrence087.occurrence'],['RSL.TX1_087.Domain LIB_Instances.VL a: original width/shape/public/semantic clauses and rev3 R4 checkValuesDom(slice proof OFF_Y1 OFF_INACTIVE)']),
 ('TX2:234','NMX_R3_RegistryRoot.root','NMX_R3_RegistryRoot','forall allocations : RSL.TX2_234.Args -> RSL.Env -> Nat -> Bool, RSL.TX2_234.RowSpec_234 LIBB_PoolLib.library LIBB_PoolLib.deployed (NMX_R3_RegistryRoot.authenticate allocations)','NMX_R3_RegistryRoot.authenticate',['NMX_R3_RegistryEmittedLink.source','NMX_R3_RegistrySource.factor','NMX_R3_RegistrySource.erase_root','NMX_R3_RegistryRun.sound','NMX_R3_RegistryTop.fold','NMX_R3_RegistryNativeFold.native','NMX_R3_RegistryProjectionRef.reference','NMX_R3_RegistryIds.pool','NMX_R3_RegistryIds.registry'],[])]:
 children=[]
 for f in by[row]['canonical_callees']:
  c=next(c for c in base['rows']if c['transaction']==by[row]['transaction']and c['function']==f)
  assert c['status']=='CLOSED'or c['row']=='TX1:137';children.append(dict(row=c['row'],status=c['status'],roots=c['root_owners'],function=f))
 reviews.append(dict(row=row,candidate=name,owner=owner,producer=producer,statement=statement,revision=3,status='STATIC_REVIEW_PASS_GATE_PENDING',gate_admitted=False,source_route='(bm) fresh actual frozen body emission; (bc) audit',remaining_parameters=[],source_chain=chain,canonical_children=children,own_input_clauses=own,basis_obligation_statement_hash=by[row]['obligation_statement_hash'],allocation='all Result/abort/diverge/ordered-prefix arms retained; arbitrary allocation choices are genuine statement inputs, not success hypotheses',finding094='Parent-only parseShape length-domain mismatch; 137 uses parsePrefix, 087 front never calls parseShape; neither child RowSpec consumes Ref094. No promotion094.'if row.startswith('TX1')else None))
reviews.insert(2,old217)
put('CANDIDATE_REVIEW',dict(candidates=reviews,gate='PENDING',security_target_established=False))
clauses=[]
for c in reviews:
 for kind in ['caller_domain_obligations','inventory_domain_obligations']:
  for z in by[c['row']]['obligation'][kind]:clauses.append(dict(row=c['row'],kind=kind,original=z,status='REVIEWED_GATE_PENDING',discharged_by=c['candidate'],note='Exact original clauses retained. SAME reached argument/provenance derived by full root; own input clauses remain in canonical RowSpec domain and upstream caller.'))
put('CLAUSE_REVIEW',dict(original_clauses=clauses,own_input_clauses={c['row']:c['own_input_clauses']for c in reviews},notes='136 finishInputDom supplied internally in137 by same successful parse/public/begin; 179 Semantic and canonical Verified at same successful137 return proved internally in087. rev3 R4 remains087 own caller clause.'))
assert not subprocess.check_output(['git','diff',F,'HEAD','--','crates','programs/r1-cost-probe','Cargo.lock'])
assert not subprocess.check_output(['git','diff','b936275465600469312d1f058cdc91ea2a11f3dc','HEAD','--','programs/aspis-pool'])
put('FROZEN_SOURCE_CHECK',dict(status='PASS',source=F,pool='b936275465600469312d1f058cdc91ea2a11f3dc',method='git diff frozen HEAD -- paths: byte identical',rebuild_trigger=False,ELFs='Inherited pins, not rebuilt: default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4; devnet63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299; Pool e0e49c344d35575116c0359450315ea4334bfb03006551727f67c04a8cfe09dc'))
print('NNK static review PASS; gate pending; no row credit')
