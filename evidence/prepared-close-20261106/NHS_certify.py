"""Additive gates; unchanged NFK certificate_checks/materialize_recipe/row_checks/admit.
Checks only. No solver run, predecessor write, graph pruning or trust removal.
"""
from pathlib import Path
import sys,json,lzma,hashlib,re,copy,collections,importlib.util,subprocess
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parents[1]
H=lambda b:hashlib.sha256(b).hexdigest()
def J(p):return json.loads(Path(p).read_bytes())
def archived(p):
 p=Path(p)
 if p.is_file():return p.read_bytes()
 x=J(str(p)+'.REFERENCE.json')
 assert x['stored_once']=='NHS_EXPECTED_IMPORTS.jsonl' and x['encoding']=='raw'
 b=(E/x['stored_once']).read_bytes()
 assert H(b)==x['sha256'] and len(b)==x['bytes']
 return b
def put(n,x):(E/n).write_text(json.dumps(x,indent=1)+'\n')
def load(p):
 spec=importlib.util.spec_from_file_location('NHS_pinned_NFK',p);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
NFK=load(R/'evidence/ledger6-20261104/NFK_validate.py')
LIMITS={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
STD={'propext','Classical.choice','Quot.sound'}
class Support:
 def support(self,c):
  for x in NFK.walk(c):
   if isinstance(x,dict) and {'path','sha256'}<=x.keys():assert H((R/x['path']).read_bytes())==x['sha256'],x['path']
def pins(ns):return [dict(path=str((E/n).relative_to(R)),sha256=H((E/n).read_bytes()))for n in ns]
def receipt(a,status):
 r=J(E/a/'receipt.json');ad=J(E/(a+'-admission.json'))
 assert r['exit_status']==status and ad['exit']==0 and ad['reservation']['allowed']is True
 assert r['limits']==LIMITS and int(r['swaps'])==0
 for n,h in r['source_hashes'].items():assert H(archived(E/a/'sources'/n))==h,(a,n)
 return r
def native_pair(n):
 rs=[]
 for num,status in [(n,0),(n+1,1)]:
  a=f'NHS_K{num:03}';r=receipt(a,status);rs.append(r);log=(E/a/'stdout.log').read_text()
  assert 'VERIFICATION:- '+('FAILED'if status else'SUCCESSFUL')in log
  assert 'timed out'not in log.lower()and 'unwinding assertion'not in log.lower()
  if status:assert 'Failed Checks:'in log and re.search(r'\*\* 1 of \d+ failed',log)
  assert J(E/(a+'-graph-check.json'))['graph_matches_frozen']
  lock=J(E/(a+'-lock-check.json'));assert lock['unchanged']and lock['before']==lock['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
  assert not J(E/(a+'-source-check.json'))['errors']
  assert r['env']['CARGO_NET_OFFLINE']=='true'and r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
  gate=(E/a/'sources/NHS_gate.py').read_text();assert 'ad8efb63d8ff791274c91eff9ccc5b9fb126f5a3ac7f27aa811ca11b8e25c138'in gate
 assert rs[0]['module']==rs[1]['module']
 assert '--cfg NHS_invert'not in rs[0]['env']['RUSTFLAGS']and '--cfg NHS_invert'in rs[1]['env']['RUSTFLAGS']
 assert rs[0]['source_hashes']==rs[1]['source_hashes']
 return dict(positive=f'NHS_K{n:03}',control=f'NHS_K{n+1:03}',module=rs[0]['module'])
def audit():
 a=J(E/'NHS_AUDIT.json');assert a['status']=='PASS'and a['raw_roots']==60 and a['all_raw_roots_standard']
 NFK.fixtures(a['fixtures']);expected=sum(J(E/'NHS_AUDIT_ROOTS.json')['groups'],[])
 assert len(a['results'])==len(expected)==len(set(expected))==60
 assert {r['root']for r in a['results']}==set(expected)
 assert all(r['equal']and set(r['walked_axioms'])<=STD for r in a['results'])
 for n in range(50,60):receipt(f'NHS_L{n:03}',0)
 assert len(receipt('NHS_L050',0)['print_axioms'])==47
 loaded=[json.loads(l)for l in (E/'NHS_LOADED_scan.jsonl').read_text().splitlines()]
 assert len(loaded)==a['modules']==13712
 assert all(not r['dangling']and not r['duplicate_owners']and r['imports_match']for r in loaded)
 assert a['scan_exit']==a['dangling']==a['incompatible_owners']==a['import_mismatches']==0
 core=(E/'NHS_ProofDriver.lean').read_text().split('  let env ←',1)[1]
 original=(R/'evidence/axaudit2-20261102/NEP_Driver.lean').read_text().split('  let env ←',1)[1]
 assert core==original
 receipt('NHS_L060',0);restore=receipt('NHS_L061',0)
 assert len(restore['print_axioms'])==4
 NFK.standard_prints(restore['print_axioms'])
 closure=lzma.decompress((E/'NHS_CLOSURE_PINS.json.xz').read_bytes())
 assert H(closure)==(E/'NHS_CLOSURE_PINS.json.sha256').read_text().strip()
 assert len(json.loads(closure)['selected_objects'])==30305
 assert J(E/'NHS_EXPORT.json')['tools_unchanged']
 success={}
 for m in J(E/'NHS_MODULES.json'):
  h=H((E/(m+'.lean')).read_bytes());matches=[]
  for p in E.glob('NHS_L???/receipt.json'):
   rc=J(p)
   if rc['exit_status']==0 and rc['source_hashes'].get('NHS_generated/'+m+'.lean')==h:matches.append(p.parent.name)
  assert matches,m;success[m]=matches[-1]
 return success
PACKETS={
 'M31::to_le_bytes':('NFW_OriginalSerializer.sourceBytes / NGT caller serializer','canonical SAME inactive value; literal fixed32 payload and four-limb packing; deployed F3M inactive source'),
 'WideExact::to_le_bytes':('NFW_OriginalSerializer.sourceBytes / NGC_KNE_Writer.cohort_program_eq','same canonical carrier, four fixed limb bytes and unchanged borrowed source'),
 'SemanticTranscript<H>::state':('AspisR1.NHS_Seed.state; NHS_K009/K010','literal immutable projection of SAME sem.transcript; arbitrary32 bytes; no digest value assertion'),
 'Transcript<H>::new':('AspisR1.NHS_Seed.start; NFW_K011/K012; NGC_DigestBridge.forwarding','S2; actual29/1/32 descriptors; SAME32-byte reply; all3 parts within NGC closed runtime forwarding domain; no global167 promotion'),
 'Transcript<H>::queries':('AspisR1.NHS_QueryPacket.source/domain; NHK_Invocation.producer; NGQ_TRANSCRIPT.actual_queries','SAME row30/31/final_message2048, complete Result/state/events; returning pair projects to NGN QLog; no global168 promotion in this delta'),
 'Transcript<H>::scalar':('AspisR1.NGT_CallerInterface.scalar; NHS_ConstructorDomain.reached; NHS_FoldDomain.bound','native rows27/28/29/30<=95; y1=928, serialized32,round0=224,fold256<=2048; SAME reply and frame'),
 'Transcript<H>::scalar_k':('AspisR1.NGT_CallerInterface.scalar_k; NHS_ConstructorDomain.reached','derived row31/32<=95,empty payload; SAME post-query transcript/rho/final state'),
 'Variant::folds':('NHL_PreparedOpening.double; NFW_K069/K070/K099/K100','actual S2 View and one/two-fold branch, same round1 and actual optional payload'),
 'prepared_claim':('NGU_PreparedClaim.packet; NGY_Thread; NHL_PreparedRecompose.source','SAME sem,y1,inactive,kappa,powers29; derived gamma/kappa/powers canonical; semantic finish/compact464/expansion928 retained root provenance, not child success'),
 'powers':('NFW_PowersCohort.source; NHS_PreparedPacket.source','canonical SAME gamma derived at scalar stage; fixed29 full overwritten scratch; Lean-discharged multiplication only'),
 'CM31::write_le_bytes':('NGC_KNE_Writer.cohort_program_eq / revalidated NFT native packet','SAME canonical fields from NHS_NFWObligation.source; writer116 transitions with actual output windows'),
 'QM31::write_le_bytes':('NGC_KNE_Writer.cohort_program_eq / revalidated NFT native packet','SAME canonical field, exact borrowed 16-byte writer window and preserved frame'),
 'Variant::tag':('NGC_KNE_Writer.cohort_program_eq','S2 from SAME prepared output, exact byte tag'),
 'checkpoint_size':('NGC_KNE_Writer.cohort_program_eq / NGC_KNE_Schedule.derivedSchedule','S2 exact fixed cap; every116-step len+size<=cap'),
 'SolanaDigest::digest':('NGC_DigestBridge.forwarding; NGC_KNE_Writer.cohort_program_eq','SAME hp/hu/hc ordered byte descriptors, max9 parts and each<=57607; reply returned unchanged; SHA256=H retained trust')}
COMMON='P6/D188 option-A native semantic transport RECLASSIFICATION, retained source/compiler/library/Std/allocator/Drop/ABI/Aeneas/source-to-ELF and runtime realizations; reviewed claim transcription (ah); no trust removed.'
def build():
 successful=audit();native=[native_pair(n)for n in [1,3,5,7,9]]
 reuse=J(E/'NHS_REVALIDATED_REUSE.json');assert reuse['status']=='PASS'and reuse['pairs']==16
 for n,h in reuse['inputs'].items():assert H((R/n).read_bytes())==h
 assert J(E/'NHS_CORRESPONDENCE.json')['status']=='PASS'
 assert len(J(E/'NHS_CORRESPONDENCE.json')['checks'])==9
 raw=lzma.decompress((R/'evidence/ledger10-20261106/NHO_LEDGER.json.xz').read_bytes())
 assert H(raw)==(R/'evidence/ledger10-20261106/NHO_LEDGER.json.sha256').read_text().strip()
 base=json.loads(raw);by={r['row']:r for r in base['rows']};assert len(by)==599
 NFK.BASE_CREDITS=base['NEZ_credits'];edges=[];certs={};candidates={};functions=[]
 for rid,root,domain in [
 ('TX1:179','AspisR1.NHS_PreparedPacket.source','Reached fixed-width S2 View (proof57607) from actual prepare prefix; original semantic-finish and compact464/expanded928 provenance; valid original carriers; linked primitive runtime/reduction observations. Full Error/fail/div cuts retained; same eleven pre-return fields and Box/frame. No constructor success/output equality premise.'),
 ('TX1:186','AspisR1.NHS_CheckpointPacket.source','SAME adopted prepare result and scratch, actual S2 accumulator/pending allocation and reservation Result, actual ten-query return and SAME pending.finish; local source observations, never a whole writer or TX1 success/equality premise. Fields/g canonicality and initial invariant derived.')]:
  row=by[rid];assert row['composed_status']=='OPEN'
  local=[]
  for f in row['canonical_callees']:
   key=f.split('::',1)[1];law,dom=PACKETS[key]
   e=dict(edge=row['function']+' -> '+f,caller_row=rid,callee=f,status='CLOSED',certificate='NHS::'+rid+'::'+key,law=law,domain=dom,domain_established=True,selected_local_packet=True)
   edges.append(e);local.append(e)
  external={o['id']:dict(classification='same-execution native staged cut plus exact emitted/frame law; retained physical realization',detail=o['call'],packet='NGN_FRAME/NHL for179; NGC116 schedule/writer/copy controls for186')for o in row['caller_domain_obligations']if 'callee'not in o}
  cert=dict(id='NHS::'+rid,row=rid,subject=row['function'],function=row['function'],frozen_body_sha256=row['frozen_body_sha256'],domain=domain,top_hypotheses=[COMMON],inner_hypotheses_remaining=[],model_root=root,route='(ai)',cohort='NGK_COMBINED_IMPORT',external_obligations=external,native=native,callee_edges=local,support=pins(['NHS_COMPOSITION.md','NHS_STUBS.md','NHS_AUDIT.json','NHS_REVALIDATED_REUSE.json','NHS_CORRESPONDENCE.json','NHS_COMBINED_IMPORT.lean','NHS_NFWObligation.lean','NHS_PendingSource.lean','NHS_CheckpointPacket.lean','NHS_PreparedPacket.lean','NHS_QueryPacket.lean','NHS_NewPort.lean']))
  cert['semantic_review_sha256']=H(json.dumps(cert,sort_keys=True).encode());NFK.certificate_checks(Support(),cert)
  candidate=NFK.materialize_recipe(row,cert,'NHS',{'edges':edges})
  # Replace stale active claim alternatives by the exact selected local packets;
  # canonical callee graph is not changed and no global child row is promoted.
  for ob in candidate['caller_domain_obligations']:
   if 'callee'in ob:ob['callee_claims']=[next(e['certificate']for e in local if e['callee']==ob['callee'])]
  assert not NFK.row_checks(candidate,row,cert)
  candidates[rid]=('NHS',candidate);certs[rid]=cert
  functions.append(dict(function=row['function'],rows=[rid],status='CLOSED',route='(ai)',model_root=root,inner_hypotheses_remaining=[],frozen_body_sha256=row['frozen_body_sha256']))
 # NHO adds twelve NGB occurrences without NFK's historical obligation schema.
 # Run unchanged NFK on its schema-compatible rows, retain the twelve byte-for-
 # byte, then additionally check every selected new edge against the FULL599.
 # This adapter cannot admit or change an NGB occurrence or a canonical edge.
 compatible=copy.deepcopy(base)
 compatible['rows']=[r for r in base['rows']if 'caller_domain_obligations'in r]
 opaque={r['row']:r for r in base['rows']if 'caller_domain_obligations'not in r}
 assert len(opaque)==12 and all(r.get('NGB_new_occurrence')for r in opaque.values())
 checked=NFK.admit(compatible,candidates,certs,{'NHS':list(candidates)})
 checkedby={r['row']:r for r in checked['rows']}
 out=copy.deepcopy(base);out['rows']=[checkedby.get(r['row'],r)for r in base['rows']]
 after={r['row']:r for r in out['rows']}
 assert all(after[r]==by[r]for r in opaque)
 denied={q for r in out['rows']if r['composed_status']!='CLOSED'for q in r['selected_claims']}
 accepted={q for r in out['rows']if r['composed_status']=='CLOSED'for q in r['selected_claims']}
 for rid in candidates:
  assert not any((set(o.get('callee_claims',[]))&denied)-accepted for o in after[rid]['caller_domain_obligations'])
 assert all(after[r]['composed_status']=='CLOSED'for r in candidates)
 assert all(after[r]['composed_status']==by[r]['composed_status']for r in by if r not in candidates)
 assert all(after[r]['canonical_callees']==by[r]['canonical_callees']and after[r]['frozen_body_sha256']==by[r]['frozen_body_sha256']for r in by)
 tests=[];rid='TX1:179';c=candidates[rid][1];cert=certs[rid]
 for label,mut in [('body hash',lambda x:x.update(frozen_body_sha256='0'*64)),('undischarged hypothesis',lambda x:x['named_hypotheses'][0].update(discharged_by=None)),('open dependency',lambda x:x.update(open_transitive_dependencies=['open'])),('no selected claim',lambda x:x.update(selected_claims=[])),('open caller domain',lambda x:x['caller_domain_obligations'][0].update(status='OPEN'))]:
  bad=copy.deepcopy(c);mut(bad);assert NFK.row_checks(bad,by[rid],cert);tests.append(label)
 for label,mut in [('bad review seal',lambda x:x.update(domain='bad')),('residual inner hypothesis',lambda x:x.update(inner_hypotheses_remaining=['open']))]:
  bad=copy.deepcopy(cert);mut(bad)
  try:NFK.certificate_checks(Support(),bad)
  except(ValueError,AssertionError):tests.append(label)
  else:raise AssertionError(label)
 try:NFK.materialize_recipe(by[rid],cert,'NHS',{'edges':[]})
 except ValueError:tests.append('missing call-domain edge')
 else:raise AssertionError('missing edge accepted')
 put('NHS_CERTIFICATES.json',certs);put('NHS_EDGES.json',dict(root_rows=list(candidates),edges=edges,canonical_graph_changed=False))
 counts=dict(collections.Counter(r['composed_status']for r in out['rows']))
 put('NHS_LEDGER_DELTA.json',dict(baseline='evidence/ledger10-20261106/NHO_LEDGER.json.xz',baseline_sha256=H(raw),newly_closed=list(candidates),new_rows=2,new_functions=2,counts_after=counts,unchanged_other_statuses=True,canonical_graph_changed=False,validator='unchanged NFK.certificate_checks/materialize_recipe/row_checks/admit plus stricter NHS native/source/domain/ax2/import gates',schema_adapter=dict(NFK_compatible_rows=587,NGB_immutable_passthrough=12,full599_selected_claim_check=True),checks_removed=0,mutations_rejected=tests,target_established=False))
 put('NHS_CLOSED.json',dict(frozen_revision=base['frozen_revision'],status='CLOSED-CONDITIONAL',route='(ai)',headline='AspisR1.RPx_Deployed.deployed',cohort='NGK_COMBINED_IMPORT',semantic_slots=dict(digest=43,error=44),functions=functions,new_composed_rows=2,new_composed_functions=2,successful_modules=successful,trust=dict(classification='RECLASSIFICATION',retained=COMMON,added=[],removed=[]),cold_release_replay=False,security_target_established=False,budget_used=dict(kani=10,lean_support=61,extraction=0),audit='NHS_AUDIT.json',reuse='NHS_REVALIDATED_REUSE.json'))
 put('NHS_VALIDATION.json',dict(status='PASS',validator_sha256=H((R/'evidence/ledger6-20261104/NFK_validate.py').read_bytes()),checks_removed=0,mutations_rejected=tests,rows=list(candidates),after=counts,admitted_rows={r:after[r]for r in candidates}))
 print(json.dumps(dict(status='PASS',rows=list(candidates),counts=counts,mutations_rejected=len(tests))))
if __name__=='__main__':build()
