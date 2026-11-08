from pathlib import Path
import json,lzma,copy,hashlib,subprocess
E=Path(__file__).resolve().parent;P=E.parent/'ledger28-20261111';H=lambda b:hashlib.sha256(b).hexdigest()
def raw(p):
 p=Path(p)
 if p.exists():return p.read_bytes()
 if Path(str(p)+'.xz').exists():return lzma.decompress(Path(str(p)+'.xz').read_bytes())
 return subprocess.check_output(['git','show','HEAD:'+str(p)])
def J(p):
 b=raw(p);return json.loads(lzma.decompress(b)if str(p).endswith('.xz')else b)
def put(n,x):(E/('NNM_'+n+'.json')).write_text(json.dumps(x,indent=1)+'\n')
basis=J(P/'NNL_LEDGER.json.xz');by={r['row']:r for r in basis['rows']};out=[]
rows=[('TX1:345','AspisR1.NNG_ActualCandidate345.candidate','4d34fbfc294','NNG_TotalProducer345.producer',[]),('TX1:344','AspisR1.NNG_Candidate344.candidate','d3fcd82238b','NNG_Candidate344.producer',[]),('TX2:233','NMX_R4_Authentication.root','2f5787475aa','NMX_R4_Authentication.authenticate Choices',[]),('TX2:242','NMX_R6_Validation.root','3fb6853107a','NMX_R6_Validation.validate Choices',[]),('TX2:241','NMX_R9_StageTwo.root','536c77b6e6b','NMX_R9_StageTwo.stage2 Choices',['D1: ∀ x ∈ a.accounts, RSL.TX2_241.Consistent x','D2: ∀ acc0 acc6 ck pr, a.accounts.length = 7 → a.accounts[0]? = some acc0 → a.accounts[6]? = some acc6 → acc6.bytes = .ok ck → acc0.bytes = .ok pr → pr.length = RSL.PROOF_ACCOUNT_BYTES → LIBB_V2Star.library.Root0 ck (RSL.slice pr RSL.AFTERSTATE_BYTES RSL.PROOF_ACCOUNT_BYTES)'])]
for row,root,commit,producer,domain in rows:
 r=by[row];children=[]
 for f in r['canonical_callees']:
  matches=[z for z in basis['rows'] if z['transaction']==r['transaction']and z['function']==f]
  if row=='TX2:233'and f.startswith('crates/aspis-core/src/field'):
   children.append(dict(function=f,status='RECLASSIFIED_SPURIOUS_BY_NAME',row=matches[0]['row']if matches else None,evidence='TCK_REPORT §5 / RSL_TX2_233: actual u64 checkpoint_sequence.to_le_bytes PDA seed; edge retained'));continue
  assert len(matches)==1,(row,f)
  c=matches[0];assert c['status']=='CLOSED'or c['row']in[z[0]for z in rows],(row,c['row'])
  children.append(dict(row=c['row'],function=f,basis_status=c['status'],root_owners=c['root_owners'],same_arguments='Derived internally at the original source call, no independent child outcome'))
 out.append(dict(row=row,theorem=root,candidate_commit=commit,implementation=producer,own_input=domain,domain='True'if not domain else'canonical RSL D1/D2',library='LIB_FullInstances.VL/P/C (NNG) or LIBB_PoolLib.library/deployed and canonical LIBB_V2Star.library (NMX)',allocation='Fixed always-success producer interpretation under ledger28 precedent'if row.startswith('TX1')else'Universally quantified primitive233 Choices, same as CLOSED234; no allocation-success premise',canonical_children=children,basis_obligation_statement_hash=r['obligation_statement_hash'],gate_admitted=False,gate_status='STATIC_PASS_REPLAY_PENDING',source_chain='NNM_EMISSION_REVIEW.json / NNM_SYNTAX_ASSOCIATION.json',consumes_trust=['ReviewedTranscription-TX1:344']if row=='TX1:344'else[]))
put('CANDIDATE_REVIEW',dict(candidates=out,gate='PENDING',security_target_established=False,provisional_NNG_Candidate345_credited=False,TGA_G1='Not in344 dependency graph; OPEN for333/330',TGB_1='Only weak G1b top composition; canonical241 fixes V0-star'))
def walk(v):
 if isinstance(v,dict):
  if isinstance(v.get('id'),str)and v['id'].startswith(('NKW-caller:TX2:233','NLG-caller:TX2:233')):yield v
  for z in v.values():yield from walk(z)
 elif isinstance(v,list):
  for z in v:yield from walk(z)
clauses=[]
for z in {z['id']:z for z in walk(by['TX2:233']['obligation'])}.values():
 inventory='inventory:U16'in z['id']
 clauses.append(dict(row='TX2:233',id=z['id'],original=z,status='DISCHARGED_PENDING_GATE',discharged_by='NMX_R4_Authentication.root',proof_support=['NMX_R4_BoxBinding.master','NMX_R4_BoxBinding.checkpoint','NMX_R4_SourceFold.source','NMX_R4_ProjectionRef.reference'],disposition='U16 inventory is the grouped unit checklist, not an extra precondition of total Box decoders.233 guards establish its reached authentication facts; SAME scan/reconstruct components are owned by242 (NMX_R5_Native242.full / NMX_R6_Validation.root). No successful caller/child assumption is introduced.'if inventory else'All immutable slices/results and allocation stop/frame interpretation discharged at SAME E008 wrapper, with CLOSED raw152/153 decoder; allocator/std trust retained.'))
assert len(clauses)==8
for parent in ['TX2:241','TX2:240','TX2:221','TX2:213']:
 clauses.append(dict(row=parent,id=f'NLG-upstream:{parent}:TX2:124:native-input',status='DISCHARGED_PENDING_241_GATE',discharged_by='NMX_R9_StageTwo.root',proof_support=['NFY_NFJ_Scanner.tag_domain','NMS_R2N_ScanRegular.source_return','LIBB_ScannerExtent.extent','NMS_R2Facts242.successful','NMS_R2Domains.entered'],S2='Frozen scan_proof_buffer lines780-806 checks bytes[688+8] = Variant::S2.tag()=2 before every Ok; CLOSED226 native/source bridge NFY_NFJ_Scanner.result_state_effects + NFY_NFJ_Comparison.completion.242 calls it on SAME accounts[0] bytes before reconstruct;241 reads same immutable proof and guards extent, then passes proof[688..58295].No entered064 path bypasses successful scan.',reservation='Same Env carries actual Reservation; no allocation-success assumption',extents='57607 from scan and proofEnd guard;publicBytes<=1880 from SAME encoder length guard;Root0 separate D2'))
# Register verbatim canonical own clauses at the only parent occurrence, per(bf)(2).
src=Path('evidence/rowspec-lead-20261107/RSL_TX2_241.lean').read_text();start=src.index('def Domain (V : V2Lib)');end=src.index('\ndef RowSpec_241',start);literal=src[start:end]
callers=[dict(id='NNM-caller:TX2:240:TX2:241:D1',caller='TX2:240',callee='TX2:241',kind='own-input-upward',required='∀ x ∈ a.accounts, RSL.TX2_241.Consistent x',status='OPEN',owner='NMV_ canonical240 instantiation',support='Snapshots derive D1; no240 root credited in this gate'),dict(id='NNM-caller:TX2:240:TX2:241:D2',caller='TX2:240',callee='TX2:241',kind='own-input-upward',required=out[-1]['own_input'][1].removeprefix('D2: '),status='OPEN',owner='NMV_ canonical240 / entry Root0 provenance',support='Canonical Root0 retained; not weak G1b. Domain240 transports D2; no240 root credited')]
for z in callers:
 z.update(caller_occurrence='RSL.TX2_240.Ref after snapAll and clock: Spec.call at SAME ⟨a.program_id,r.1,a.data,c⟩',callee_arguments='(⟨a.program_id,r.1,a.data,c⟩ : RSL.TX2_241.Args)',required_at_occurrence='Corresponding conjunct of canonical241_Domain_verbatim at this SAME tuple')
put('CLAUSE_REVIEW',dict(clauses=clauses,registered_caller_clauses=callers,canonical241_Domain_verbatim=literal,canonical241_Domain_sha256=H(literal.encode()),rule='(bf)(2):241 credited on own D1/D2; callers remain accountable',TGB_2=dict(status='DISCHARGED_INSIDE242',lemma='NMX_R4_NMSCarrier.auth',source_chain=['NMX_R5_Native242.full','NMX_R4_NMS242Instantiation.fold','LIBB_AuthCarrier.exact_carrier'],domain='Native Auth.erase image; arbitrary mathematical Args handled by exact same-order port, including oversized-proof panic'),TGB_3='ProjectionRef.reference at233; NMX_R6_Port242 and NMX_R7_PortLaw241 preserve per-field stop/error/panic behaviour, no uniform oversized Err fallback',TGB_1='OPEN TOP:G1b only; canonical241 is V0-star, not parametric in V'))
for paths,rev in [(['crates','programs/r1-cost-probe','Cargo.lock'],'4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'),(['programs/aspis-pool'],'b936275465600469312d1f058cdc91ea2a11f3dc')]:
 assert not subprocess.check_output(['git','diff',rev,'HEAD','--',*paths]);assert not subprocess.check_output(['git','diff','HEAD','--',*paths])
put('FROZEN_SOURCE_CHECK',dict(status='PASS',frozen='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',Pool='b936275465600469312d1f058cdc91ea2a11f3dc',rebuild_trigger=False,ELFs=J(P/'NNL_FROZEN_SOURCE_CHECK.json')['ELFs'],ELF_claim='Inherited pins only; no shipped change, no rebuild'))
print('NNM five static candidates and caller clauses prepared; no credit before whole gate')
