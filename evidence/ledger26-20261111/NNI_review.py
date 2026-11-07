"""Read-only retained-certificate review; no prover/extraction invocation."""
from pathlib import Path
import json,lzma,hashlib,subprocess,re
E=Path(__file__).resolve().parent;R=Path.cwd();T=E.parent/'tx1-principal-20261111';Q=E.parent/'tx2-auth-20261111';F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';H=lambda b:hashlib.sha256(b).hexdigest()
def raw(p):
 if p.exists():return p.read_bytes()
 if Path(str(p)+'.xz').exists():
  b=lzma.decompress(Path(str(p)+'.xz').read_bytes());assert H(b)==Path(str(p)+'.sha256').read_text().strip();return b
 rel=str(p.relative_to(R)) if p.is_absolute() else str(p)
 r=subprocess.run(['git','show','HEAD:'+rel],capture_output=True)
 if r.returncode==0:return r.stdout
 b=lzma.decompress(subprocess.check_output(['git','show','HEAD:'+rel+'.xz']));assert H(b)==subprocess.check_output(['git','show','HEAD:'+rel+'.sha256'],text=True).strip();return b
def J(p):return json.loads(raw(p))
def put(n,x):(E/('NNI_'+n+'.json')).write_text(json.dumps(x,indent=1)+'\n')
base=json.loads(lzma.decompress((E.parent/'ledger25-20261111/NMQ_LEDGER.json.xz').read_bytes()));by={r['row']:r for r in base['rows']}
pins=J(T/'NNG_emitted/verify_finish/NNG_PINS.json');bc=J(T/'NNG_BC_AUDIT.json');erc=J(T/'NNG_E001/receipt.json')
assert pins['frozen_revision']==F and pins['aeneas_exit']==pins['charon_exit']==erc['exit_status']==0
assert pins['lock_before']==pins['lock_after']==H(subprocess.check_output(['git','show',F+':Cargo.lock']))
assert pins['root']=='crate::r1_semantic::verify_finish'
for rel,h in pins['outputs'].items():assert H(raw(T/'NNG_emitted/verify_finish'/rel))==h
assert H(raw(T/'NNG_emitted/verify_finish/verify_finish.llbc'))==pins['llbc_sha256']
assert bc['status']=='PASS_NO_POST_LOOP_PATTERN' and bc['emission_sha256']==pins['outputs']['raw/NNG_verify_finish/Funs.lean']
for s in bc['spans']:assert H(subprocess.check_output(['git','show',F+':'+s['file']]))==s['source_sha256']
for a in [358,359,362]:assert J(T/f'NNG_L{a:03}/receipt.json')['exit_status']==0
children=[]
for callee in by['TX1:136']['canonical_callees']:
 row=next(r for r in base['rows']if r['transaction']=='TX1'and r['function']==callee);assert row['status']=='CLOSED';children.append(dict(row=row['row'],function=callee,roots=row['root_owners'],owner=row['owner_module']))
lib=raw(E.parent/'lib-20261111/LIB_VLib.lean').decode();fields=[]
for name,definition in re.findall(r'^  (\w+) := ([\w.]+)$',lib,re.M):fields.append(dict(field=name,definition=definition))
source_chain=['NNG_TreeEmission.erase_tree','NNG_Observed136.producer_tree','NNG_DEnvObserved136.producer_tree','NNG_DRowSpec136.fold','NNG_Packet136.closed','AspisR1.NNG_Candidate136.candidate']
review136=dict(row='TX1:136',candidate='AspisR1.NNG_Candidate136.candidate',owner='NNG_Candidate136',producer='AspisR1.NNG_Producer136.producer',statement='RSL.TX1_136.RowSpec_136 LIB_VLib.library NNG_Producer136.producer',status='STATIC_REVIEW_PASS_GATE_PENDING',gate_admitted=False,revision=3,source_route='(bm) fresh receipted actual-body emission; (bc) passes',frozen_revision=F,extraction_receipt='NNG_E001',emission_sha256=bc['emission_sha256'],source_chain=source_chain,library_fields=fields,canonical_children=children,concrete_installation=['NNG_Representation136.project/calls/input','NNG_ConcreteCalls136.calls','NNG_LIBRounds.call_model','NNG_LIBClaims','NNG_LIBTerminal','NNG_LIBRecords','NNG_LIBField','NNG_CheckedCalls136','NNG_AllReached136','NNG_Packet136.closed'],remaining_parameters=[],own_input_clauses=J(T/'NNG_CALLER_CLAUSES.json')['136'],caller='TX1:137',caller_status='OPEN',scope='all Result/error/abort/diverge arms and SAME typed-tree ordered prefix; raw canonicality of running/masked derived internally, never added as caller clauses',trust='Existing extraction/std/runtime and native child method retained; (bm) increased reliance on existing extraction item, not new cryptographic trust',basis_obligation_statement_hash=by['TX1:136']['obligation_statement_hash'])
review136['own_input_expansion']=['LIB_VPublicDomain.publicDigestDom pub','LIB_VPublicDomain.publicAssetDom pub','p.source.val.length <= 57607']
review136['original_NNG_clause_note']=review136['own_input_clauses']
review136['own_input_clauses']=[dict(predicate='LIB_VLib.library.finishInputDom a.public_ a.prefix_ a.transcript a.challenges',definition='RSL.TX1_136.Domain LIB_VLib.library a',expanded=review136['own_input_expansion'],classification='original136 own-input predicate at SAME entered arguments, caller clause of OPEN137')]
review136['carrier_provenance']={'Prefix':'LIB_VCarriers.Prefix stores SAME source Slice, parsed Prefix and parse_eq on that source; supplied by same parse returned arm in137, not an extra library/representation premise.','Challenges':'canonical scalar subtypes supplied from SAME begin evaluator; running/masked canonicality derived internally.','domain_source':'LIB_VDomains.finishInputDom; no RowSpec, acceptance or source/model correspondence proposition is hidden in the predicate.','137_support':'LIB_VDomains.finish_of_eval / NNG_Caller136From137 / NNG_FinishInput137; support only, no137 row credit.'}
patch=raw(E.parent/'kani-mitig-20261028/KMX_copy_stubs.patch');assert H(patch)=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
runs=[]
for n in [5,6,8,9,10,11,12,13,15,16,17,18,19,20,25,26,27,28]:
 a=f'NMX_K{n:03}';r=J(Q/a/'receipt.json');g=J(Q/(a+'-graph.json'));log=raw(Q/a/'stdout.log').decode();wanted=0 if n in [5,8,9,12,15,17,19,25,27] else 1
 assert r['exit_status']==wanted
 assert g['graph_matches_frozen'] and g['offline'] and g['lock_unchanged'] and g['lock_before_sha256']==g['lock_after_sha256']==pins['lock_before']
 assert g['KMX_patch_sha256']==H(patch)
 features=[v for k,v in g['features'].items()if 'programs/r1-cost-probe#'in k];assert len(features)==1 and {'pool-adapter','private-leaf-salts'}<=set(features[0])
 if n==10:assert 'Arbitrary' in log and 'VERIFICATION:- FAILED'not in log
 else:
  assert ('VERIFICATION:- SUCCESSFUL'if wanted==0 else'VERIFICATION:- FAILED')in log
  if wanted:assert 'Failed Checks:'in log
 runs.append(dict(attempt=a,verdict='COMPILE_FAILURE_NO_CREDIT'if n==10 else'PASS'if wanted==0 else'FAIL',receipt_sha256=H(raw(Q/a/'receipt.json')),log_sha256=H(log.encode()),graph_sha256=H(raw(Q/(a+'-graph.json'))),features=features[0],exit=r['exit_status'],source_hashes=r['source_hashes']))
ndb=[]
for pair in J(Q/'NMX_217_NDB_COMPONENTS.json')['pairs']:
 for entry in pair['pair']:
  a=entry['attempt'];d=R/'evidence/native-decnat-20261028';r=J(d/a/'receipt.json');g=J(d/(a+'-graph.json'));log=raw(d/a/'stdout.log').decode();assert H(raw(d/a/'receipt.json'))==entry['receipt_sha256'] and H(raw(d/(a+'-graph.json')))==entry['graph_sha256']
  assert r['exit_status']==entry['exit_status'] and g['graph_matches_frozen'] and g['offline'] and g['lock_unchanged'] and g['KMX_patch_sha256']==H(patch)
  assert ('VERIFICATION:- SUCCESSFUL'if r['exit_status']==0 else'VERIFICATION:- FAILED')in log
  if r['exit_status']:assert 'Failed Checks:'in log and 'NDB semantic law'in log
  ndb.append(dict(entry,log_sha256=H(log.encode())))
ref=J(Q/'NMX_217_REFERENCE_ROUTE.json')['reference'];assert H(raw(R/ref['path']))==ref['sha256'];assert H(raw(R/ref['emitted_path']))==ref['emitted_sha256']
review217=dict(row='TX2:217',candidate='NMX_R3_DecoderFold.root',statement='forall allocationSucceeded : Bytes -> Env -> Bool, RSL.TX2_217.RowSpec_217 (NMX_R3_DecoderFold.decode allocationSucceeded)',status='OPEN_FIDELITY_CONTROL_MISSING',gate_admitted=False,revision=3,reference=ref,native_runs=runs,inherited_native_runs=ndb,reference_roots=['NMX_R3_LaneTotal.value','NMX_R3_LanePort.pure_eq','NMX_R3_LaneAllocation.root','NMX_R3_LaneAllocation.complete'],native_step_roots=['NMX_R3_NativeStep.accepted','NMX_R3_NativeStep.rejected'],own_input_clauses=[],all_slice_lengths=True,allocation='pointwise universally quantified; successful final Box and silent abort; earlier errors introduce no allocation',segmented_composition='NMX_217_NATIVE_COMPOSITION.md source-ordered packet; native arbitrary one-step and Lean induction, not whole-buffer unwind',copy_patch_sha256=H(patch),copy_controls='All used listed component pairs fail their intended property under exact KMX patch; no separate new Kani run by ledger',trust_item='ReviewedTranscription-TX2:217',trust_status='ADDED-LEAD-20261107; option-A reclassification; unused by CLOSED rows in this gate',ruling_t_decision=dict(sufficient=False,reason='Ruling (t) requires three per-shape fidelity controls before relying on a contract for a non-Bool/non-record interface. The actual decoder length certificate K005 uses Result<Box<Lane>,ProgramError>. K006 supplies inverted ensures failure; K011 detects modifies violation; K009 passes on real body. K010 cannot generate the stub_verified caller because Result<Box<Lane>,ProgramError> lacks kani::Arbitrary and does not reach the intended assertion failure. Excluding pilot substitution does not supply this required per-shape evidence.',missing='Unimplied caller assertion must FAIL under stub_verified for the SAME Result<Box<Lane>,ProgramError> shape while PASSING on real body.',no_compile_failure_credit=True,no_renaming=True,no_kani_authorization=True),exact_blocker='NMX_K010 / NMX_shape_stub: compile failure, not matched assertion failure; ruling (t) per-shape gate incomplete',other_retired_attempts=['K001','K003','K004','K007','K014','K021','K023'],basis_obligation_statement_hash=by['TX2:217']['obligation_statement_hash'])
review217['additional_shape_obligations']=[dict(certificate='NMX_K015/K016; NMX_assign',interface='Result<(),ProgramError> with &mut [M31;8]',finding='The paired ensures FAIL establishes the segment property control, not the complete three-part per-interface ruling(t) calibration. The packet supplies no successful unimplied-caller assertion FAIL under stub_verified and matched modifies calibration for this distinct Result/mutable interface. Result<Box<Lane>,ProgramError> pilot does not transfer to it.',status='OPEN_FIDELITY_SHAPE; not a source defect',effect='Even omitting redundant length-pair reliance cannot silently waive the per-shape rule for the used assignment contract.') ]
put('CANDIDATE_REVIEW',dict(candidates=[review136,review217],security_target_established=False,gate='PENDING'))
put('PARENT_CLAUSES',dict(parent='TX1:137',helper='TX1:136',clauses=review136['own_input_clauses'],status='OPEN_CALLER_CLAUSE',proof_support='NNG_Caller136From137 and NNG_FinishInput137 are supporting proofs; no literal137 candidate or gate credit'))
print(json.dumps(dict(review136='PASS_STATIC_PENDING_GATE',review217='OPEN_MISSING_RULING_T_CONTROL',new_native_runs=len(runs),inherited_runs=len(ndb))))
