#!/usr/bin/env python3
import json,re,hashlib,collections
from pathlib import Path
O=Path(__file__).parent
raw=json.loads((O/'NBI1_REACH_DRAFT.json').read_text());ix=json.loads((O/'NBI1_COHORT_INDEX.json').read_text())
C=set(json.loads(Path('evidence/replay-deployed2-20261027/RPx_reachable-constants.json').read_text()))
fs=raw['functions'];byid={f['id']:f for f in fs}
for i,f in enumerate(fs,1):f['row']=f'F{i:03}'
# These names are consumer definitions actually present in the checked headline closure.
A={
('lib.rs','','process_r1_cost_probe_instruction'):['AspisR1.DrvC_SourceEntry.source'],
('lib.rs','SolanaDigest','digest'):['AspisR1.S2W_DigestExtraction.digest'],
('r1_pool_adapter_owned.rs','','stage1'):['AspisR1.S2W_D189Wrappers.first'],
('r1_pool_adapter_owned.rs','','stage1_owned'):['AspisR1.S2W_Outer.stage1_owned','AdapterRw.r1_pool_adapter.owned.stage1_owned'],
('lib.rs','','first_decoded'):['AspisR1.S2W_Outer.first_decoded','AdapterRw.first_decoded'],
('candidate.rs','','canonical_scan'):['Op4P_Extract.Op4P_reference.canonical_scan'],
('candidate.rs','','parse_shape'):['Op3I_Source.verifier.candidate.parse_shape'],
('candidate.rs','','wide_view'):['AspisR1SelectedWideViewV1.verifier.candidate.wide_view'],
('candidate.rs','','prepare'):['AspisR1CurrentCaller.verifier.candidate.prepare'],
('candidate.rs','','tx1'):['AspisR1CurrentCaller.verifier.candidate.tx1'],
('verifier.rs','Prepared','new'):['AspisR1PublicPreparation.PreparedScratchModel.prepare'],
('verifier.rs','','prepared_claim'):['AspisR1CurrentPreparedClaim.verifier.prepared_claim'],
('verifier.rs','','checkpoint'):['AspisR1.CheckpointBytes5Writer.writer','AspisR1.CheckpointBytesBody.fields'],
('verifier.rs','BatchedWeights','finish'):['AspisR1.Port3_FlushInstall.flush','S8Kani2MutableExtraction.batched_weights.BatchedWeights.finish'],
('verifier.rs','BatchedWeights','value'):['AspisR1BatchedWeightsExtraction.batched_weights.BatchedWeights.value'],
('verifier.rs','QueryGeometry','for_range'):['AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range'],
('r1_semantic.rs','','verify_observed'):['AspisR1PublicPreparation.S1SemanticCode.verify'],
('r1_semantic.rs','','verify_finish'):['AspisR1PublicPreparation.FinishModel.finish'],
('r1_semantic.rs','','claims'):['AspisR1ClaimsUnrolledParent.candidate_claims.claims'],
('r1_semantic.rs','','semantic_boundary'):['AspisR1SemanticCallExtraction.r1_semantic.semantic_boundary'],
('r1_semantic.rs','','semantic_value'):['AspisR1SemanticCallExtraction.r1_semantic.semantic_value'],
('r1_wire.rs',"Prefix<'a>",'parse'):['AspisR1PrefixAggregateParser.r1_wire.Prefix.parse'],
('r1_wire.rs',"ValidatedRecord<'a>",'decode_k'):['AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k'],
('sampler.rs','','circle_sample'):['AspisR1CircleSampleWrapper.sampler.circle_sample'],
('sampler.rs','','low_base_p_digits'):['AspisR1Post25Sampler.sampler.low_base_p_digits'],
('compact.rs','','expand_semantic'):['AspisS1NativeCompact.compact.expand_semantic'],
('compact.rs','','check_values'):['MultiproofParserRef.reference.check_values','Op4P_Extract.Op4P_reference.reference.check_values'],
}
A.update({
('candidate.rs','','batch_keys'):['AspisR1.Port4B_KeyInstall.keyArray'],
('candidate.rs','','sort_batch_keys'):['AspisR1.Port4B_SortInstall.key_stream'],
('candidate.rs','','batch_leaf'):['AspisR1.Port4B_LeafCode.codeFor'],
('candidate.rs','','opening'):['AspisR1.Port4B_Opening.opening'],
('candidate.rs','','slot'):['AspisR1.Port4B_SlotInstall.nodeSlot'],
('candidate.rs','','same_batch_index'):['AspisR1.Port3_BatchStd.sameIndex'],
('candidate.rs','','same_batch_leaf'):['AspisR1.Port3_BatchStd.sameLeaf'],
('compact.rs','','slot_offset'):['AspisR1.Port4B_SlotInstall.offset'],
('multiproof.rs','','node_count'):['AspisR1.Port4B_CountInstall.nodeCount'],
('multiproof.rs','','verify_in_place'):['AspisR1.Port4B_VerifyInstall.verify'],
('verifier.rs','Accumulator','new'):['AspisR1.Port3_Initial.constructor'],
('verifier.rs','BatchedWeights','new'):['AspisR1.Port3_NativePendingInstall.source'],
('verifier.rs','BatchedWeights','push'):['AspisR1.Port3_NativeRowFrame.push'],
('verifier.rs','','update_residue_row'):['AspisR1.Port3_NativeRowFrame.body'],
('transcript.rs','Transcript<H>','scalar'):['AspisR1PublicPreparation.PreparedModel.scalar'],
('transcript.rs','Transcript<H>','scalar_k'):['AspisR1PublicPreparation.PreparedModel.scalar_k'],
('transcript.rs','Transcript<H>','queries'):['AspisR1PublicPreparation.QueriesModel.queries'],
('weights.rs','','powers'):['AspisR1CurrentCaller.OriginalPreparedSource.powers','AspisR1CurrentPreparedClaim.ClaimPowers.powers'],
('r1_wire.rs','SemanticTranscript<H>','circle_validated'):['AspisR1PublicPreparation.FinishModel.circle_validated'],
})
# Bridge units deliberately keep small scalar/index/transport helpers with a consumer.
U={
'control':('Release no-op observers, trace and Variant projections','S','Release observer None, trace compiled out; S2 tag2/folds2/final_len64. No callback or oracle effect. Small projections merge into each caller.'),
'oracle':('Concrete digest backend','S','SolanaDigest::digest uses pinned hashv syscall; same parts/order and arbitrary32-byte replies under retained P1/runtime syscall trust. No SHA unwinding.'),
'field':('Field and scalar carriers','M','Canonical natural coordinates; retain exact packed carriers, checked overflow and error behavior. Multiplication uses only Lean-discharged stubs with named emitted-definition value theorems (LPh_STUBS and descendants).'),
'alloc':('Allocation and buffer initialization','M','Pinned allocator/library admission; successful length and full initialized carrier, with Allocation/abort behavior retained.'),
'public-codec':('Public statement decode, validation and afterstate encode','L','Same 1880-byte public buffer, successful fixed decoder; validated statement and same 688-byte encoded candidate. All branch-specific Transfer/Withdrawal guards and digest/field bounds.'),
'public-hash':('Poseidon and tree/public validation helpers','L','Canonical M31 inputs and exact fixed-width public/tree state; no reselected root or replacement public serialization.'),
'semantic-eval':('S1 public/Copy/semantic terminal helpers','L','Same Public, genuine parsed Claims, alpha/challenges and actual canonical decoder outputs. Reuse S1 cohort theorems read-only; native association of every helper and loop remains a caller obligation.'),
'leaf':('CLOSED opaque leaves','S','Exactly the packet domain listed below, on the same caller operands; existing bridge only, no new leaf proof.'),
'sampler':('Sampler wrappers and digit helpers','M','Arbitrary exact 32-byte block; LPk low digits on same block; ordinary/gamma canonicality and gamma nonzero. Preserve modulo/carry and typed result.'),
'parser':('Prefix/record parser and semantic expansion','M','Stored proof length57607; semantic compact range to logical13831; row framing and exact same Prefix token; LPn expansion 0..1856/0..3712; validation payload0..3712; decode N=1/28/29 and reached offsets0/29/58/87.'),
'semantic-transcript':('Semantic transcript and rounds','L','Same valid Prefix/public bytes; row-ordered blocks, two CircleRows and arbitrary digest replies; canonical 28-coefficient polynomial from same decode. Preserve first error and every attempted oracle call.'),
'opening-transcript':('Opening transcript and Prepared constructor','L','Same successful semantic finish; exact y1 length928/inactive32/round224/root32/final2048. Establish sampler domains, powers29 output identity, LPt compact464 checked/expanded same carrier, canonical kappa/gamma/inactive.'),
'shape':('Shape and canonical scan','M','Proof57607 and S2 magic/header; check_values464; echeck32/224/2272/128; all22 openings832, every M31/K field canonical; preserve first Parse.'),
'geometry':('Domain tables and query geometry','L','22 distinct query indices<262144; 0<=start<=end<=22, TX1 start0/end10; five nonzero denominators per query, flat length50. Prove nonzero product and indexed inverse vector association.'),
'dots':('Four query dots and EbyK carrier helpers','L','Exact opening832 (dot prefix608), g29 canonical from same powers; 26 base terms plus three K tails per slot; private-Q canonicality; count<4096; reuse LPn Dot.push on same state, not independent dots.'),
'keys':('Batch sort, opening and slot helpers','M','Batch0,n10,tree0/1/2; queries<262144; stable position keys; sorted unique output prefix with folded duplicates carrying identical leaves; exact source slices.'),
'multiproof':('Binary multiproof scan and in-place verifier','L','Arity Two only; 1<=d<=10<=16, sorted distinct idx<2^18; exact node_count words within fixed slot, zero padding. Retain mutable idx/val alias/frame and chronological leaf/parent digests.'),
'batch':('Three batch-tree calls','L','Same prepared queries/roots and folded root; batch0 trees0,1,2; keys/dedup/count/padding establish each multiproof domain; same shared idx/val scratch and ordered oracle log.'),
'residue':('Batched residue initialization/update/flush','L','64 canonical initial weights; raw rows U64; terms tracks same query count, at group boundary limbs<2^34; each update adds canonical power*basis without overflow; flush when terms&3=3. Finish reduces same raw rows into same64-weight allocation.'),
'accumulate':('Basis and accumulator one query step','L','S2 width64, next i<10; same pending terms=i, same rhs/power; canonical fold/node/rho and basis; establish raw update invariant, next=i+1, power/rhs exact and original weights retained until flush.'),
'query':('Query values and loop','L','Same authenticated batch0/proof/Prepared/g29; geometry start0/end10; accumulator.next=i and pending terms=i, i<10; dots/folds compare same selected field, preserve rejection and observer None. One arbitrary native step plus Lean induction to next10.'),
'prepare':('Logical allocation and verifier prepare','L','Same proof57607, validated Public and immutable physical public1880; logical buffer14759 split13831/928 with disjoint mutable windows. Produce actual semantic finish and prepared/g29 once; prove all leaf/callee domains from scan.'),
'wrapper':('SDK first wrapper and owned outer body','L','One runtime-admitted execution, three distinct accounts; readonly proof58295/public1880, writable program-owned zero checkpoint1768, allowed borrow counters and retained keys; candidate prefix688, suffix57607 and k10; snapshot/write/drop/metadata/frame and exact child effects under approved SDK trust.'),
'entry':('Entrypoint and release dispatch','M','Pinned release features pool-adapter,private-leaf-salts for BOTH default/devnet; [3,10] accepted ([3,11] reaches child rejection); account gates, same original input bytes and observer None; distinguish default route from adopted Pool headline admission.'),
'driver':('TX1 composition to checkpoint writer','L','All predecessors from same accepted run; k10,S2; accumulator next10/64 canonical weights after flush, queries22<2^18; LPm exact p/a/proof57607/public1880 with three ordered digests and output1768; no independently supplied checkpoint.'),
}
def unit(f):
 p=Path(f['file']).name;n=f['name'];owner=f['owner']
 if f['owner']=='SolanaDigest' and f['name']=='digest':return 'oracle'
 if f['name'] in ('observer','error'):return 'control'
 if f['name']=='mark' or Path(f['file']).name in ('trace.rs','transport.rs'):return 'control'
 if f['closed_leaf_packet']:return 'leaf:'+n+(':'+owner if owner else '')
 if 'aspis-core/src/field' in f['file'] or p=='scalar.rs':return 'field'
 if p=='heap.rs':return 'alloc'
 if p=='weights.rs' and n=='field':return 'field'
 if p in ('atomic_statement.rs','format.rs') or f['name'] in ('decode_digest_canonical','encode_digest_canonical','pool_v1_tree_parent'):return 'public-hash'
 if p in ('poseidon2.rs','state_only_poseidon.rs','incremental_merkle.rs'):return 'public-hash'
 if p=='pair_tree_profile.rs':return 'public-codec'
 if f['file'].startswith('programs/'):
  if p in ('lib.rs','pool_route.rs') and n in ('process_r1_cost_probe_instruction','admitted','observer','error','digest'):return 'entry'
  return 'wrapper'
 if p in ('pair_forest_terminal.rs','payment_relation.rs','pair_terminal.rs','pair_forest_accounts.rs','format.rs','atomic_statement.rs'):return 'public-codec'
 if 'aspis-statement' in f['file'] or p=='state_only_hiding.rs':return 'semantic-eval'
 if p in ('sampler.rs',):return 'sampler'
 if p=='r1_wire.rs':return 'semantic-transcript' if 'SemanticTranscript' in owner or n=='begin' else 'parser'
 if p=='r1_semantic.rs':return 'semantic-transcript'
 if p=='compact.rs':return 'parser'
 if p=='transcript.rs' or (p=='verifier.rs' and owner=='Prepared') or p=='r0_transcript.rs' or p=='weights.rs' and n=='powers':return 'opening-transcript'
 if p=='candidate.rs':
  if n=='tx1':return 'driver'
  if n=='prepare':return 'prepare'
  if n in ('parse_shape','canonical_scan'):return 'shape'
  if n.startswith('query_'):return 'query'
  if n in ('batch_tree','batch_merkle','batch_merkle_values'):return 'batch'
  return 'keys'
 if p=='fast_domain.rs' or p=='domain.rs' or p=='verifier.rs' and (owner=='QueryGeometry' or n=='batch_prefix_products'):return 'geometry'
 if p in ('fast_pairing.rs','fast_dots.rs'):return 'dots'
 if p=='multiproof.rs' or p=='merkle.rs' or p=='state_only_private_merkle.rs':return 'multiproof'
 if p=='verifier.rs':
  if owner=='BatchedWeights' or n in ('update_residue_row','residue_limb_at','power_limb_at'):return 'residue'
  if n in ('accumulate_batched_with_node','basis_at','accumulated_weight_at'):return 'accumulate'
  if n in ('circle_fold_with_inverses','line_fold_with_inverses'):return 'query'
  if owner=='Accumulator':return 'driver'
  if n=='checkpoint_size':return 'wrapper'
 return 'control' # remaining pure projections

def normowner(s):return re.sub(r'<.*','',s).replace('::','.')
# Build exact suffix index, retaining only executable definitions/abbreviations.
bylast=collections.defaultdict(list)
for name,rows in ix.items():
 for row in rows:
  if row['kind'] in ('def','abbrev','opaque') and '/XRn_' not in row['source'] and '/XRo_' not in row['source']:
   bylast[name.rsplit('.',1)[-1]].append(row)
auditowners={}
for directory in Path('evidence').glob('replay-*'):
 for ap in list(directory.glob('*axiom-audit.json'))+list(directory.glob('*declaration-audit.json')):
  ad=json.loads(ap.read_text())
  ars=ad.get('declarations',[])
  if not isinstance(ars,list):ars=ad.get('records',[])
  for ar in ars:
   if isinstance(ar,dict) and 'name' in ar and 'module' in ar:auditowners[ar['name']]={'module':ar['module'],'audit':str(ap)}
usedmodels={}
for f in fs:f['bridge_unit']=unit(f)
for f in fs:
 f['bridge_unit']=unit(f)
 key=(Path(f['file']).name,f['owner'],f['name']);names=A.get(key)
 candidates=[]
 if names is not None:
  for name in names:
   if name in C:
    rows=ix.get(name,[])
    if rows:candidates.extend(rows)
    else:candidates.append({'name':name,'module':'UNLOCATED: see finding','source':None,'line':None,'in_deployed_closure':True})
 else:
  owner=normowner(f['owner']).split('.')[-1] if f['owner'] else None
  stem=Path(f['file']).stem
  for r in bylast[f['name']]:
   name=r['name'];comment=r.get('rust_source_comment')
   same_comment=comment and comment[0]==f['file']
   if owner:
    match=('.'+owner+'.') in name
   else:match=('.'+stem+'.') in name
   if owner and not match:continue
   if not same_comment and not match:continue
   if same_comment and not match and not(comment[1]<=f['line']<=comment[2]):continue
   candidates.append(r)
 # Prefer canonical source over receipt snapshots, and pin module names independently.
 dedup={}
 for r in candidates:
  name=r['name'];score=(r.get('module')==auditowners.get(name,{}).get('module'),bool(r.get('retained_objects')), '/lean/' in r.get('source','') or r.get('source','').startswith('lean/'), 'diagnostic' not in r.get('source',''), -len(r.get('source') or ''))
  if name not in dedup or score>dedup[name][0]:dedup[name]=(score,r)
 f['cohort_definitions']=[v[1] for _,v in sorted(dedup.items())]
 f['cohort_status']='exact reached definition(s)' if dedup else 'no cohort counterpart'
 for r in f['cohort_definitions']:
  if r['name'] in auditowners:
   r['replayed_owner']=auditowners[r['name']]
   if r['module']!=auditowners[r['name']]['module']:
    r['located_source_module']=r['module'];r['module']=auditowners[r['name']]['module']
  usedmodels[r['name']]=r
 f['callees']=[{**e,'inventory_rows':[byid[k]['row'] for k in e['targets'] if k in byid]} for e in f['callees']]
 # Ambiguous field support is explicitly not promoted to a resolved type assignment.
 f['reachability']='TX1 source call closure; field-method overloads conservatively included'
 f['callee_domain_obligations']=[{'callee_row':byid[t]['row'],'unit':byid[t]['bridge_unit']} for e in f['callees'] for t in e['targets'] if t in byid]
for f in fs:
 f['iterator_operations']=sorted(set(e['expression'] for e in f['callees'] if re.search(r'\.(?:fold|map|any|all|from_fn|chunks_exact|iter|iter_mut|zip|enumerate|rev|collect)\b',e['expression'])))
# Unit dependency SCCs are allowed only inside an explicitly grouped unit; flag any remaining cycle.
units={}
for f in fs:
 u=f['bridge_unit'];base='leaf' if u.startswith('leaf:') else u
 title,estimate,domain=U[base]
 if base=='leaf':title=f['name']+' (CLOSED)';domain='Use '+f['closed_leaf_packet']+' verbatim on this SAME source carrier; see leaf domain table.'
 units.setdefault(u,{'id':u,'title':title,'estimate':estimate,'domain':domain,'members':[],'callee_bridges':set()})['members'].append(f['row'])
 if not f['closed_leaf_packet']:
  for e in f['callees']:
   for t in e['targets']:
    if t in byid and byid[t]['bridge_unit']!=u:units[u]['callee_bridges'].add(byid[t]['bridge_unit'])
# Control-only no-op mark/Variant/trace/observer is merged into its caller, not an entry dependency.
control={f['id'] for f in fs if Path(f['file']).name in ('trace.rs','transport.rs') or f['name']=='mark'}
for u in units.values():u['callee_bridges']=sorted(u['callee_bridges'])
# Emit bottom-up SCC groups so the review can see unavoidable grouping explicitly.
indices={};low={};stack=[];onstack=set();components=[]
def strong(v):
 indices[v]=low[v]=len(indices);stack.append(v);onstack.add(v)
 for w in units[v]['callee_bridges']:
  if w not in indices:strong(w);low[v]=min(low[v],low[w])
  elif w in onstack:low[v]=min(low[v],indices[w])
 if low[v]==indices[v]:
  comp=[]
  while True:
   w=stack.pop();onstack.remove(w);comp.append(w)
   if w==v:break
  components.append(sorted(comp))
for v in sorted(units):
 if v not in indices:strong(v)
ordered=[]
for i,comp in enumerate(components,1):
 for u in comp:units[u]['bottom_up_group']=i;units[u]['grouped_with']=[x for x in comp if x!=u];ordered.append(units[u])
missing=[{'row':f['row'],'function':f['id'],'unit':f['bridge_unit']} for f in fs if not f['cohort_definitions']]
result={'schema':1,'frozen_revision':'4bb3b3f51e16b4525f1d10336e2b0bcbbd775387','headline':'AspisR1.RPx_Deployed.deployed','status':'STATIC INVENTORY; native caller bridges proposed, no premise removed','source_hash_convention':'Exact frozen UTF-8 bytes from opening { through matching } inclusive; attributes/signature excluded. function_sha256 also records fn item. FibreIndex uses pinned macro template body with recorded instantiation.','closure_inputs':[{ 'file':p,'sha256':hashlib.sha256(Path(p).read_bytes()).hexdigest()} for p in ['evidence/replay-deployed2-20261027/RPx_reachable-constants.json','evidence/replay-deployed2-20261027/RPx_import-closure-check.json','evidence/replay-tops3-20261027/RPv_FJv_Top-reachable-constants.json','evidence/replay-tops3-20261027/RPv_FJv_Top-import-closure-check.json']], 'budget_used':{'Lean':0,'Kani':0,'Rust':0},'release_build_plan':'evidence/sbf-identity-20261024/recapture-plan.json','no_separate_counterpart':missing,'bridge_units':ordered,'functions':fs,'models':usedmodels}
(O/'NBI1_INVENTORY.json').write_text(json.dumps(result,indent=2)+'\n')
(O/'NBI1_MODELS.json').write_text(json.dumps(usedmodels,indent=2)+'\n')
print('functions',len(fs),'models',len(usedmodels),'no separate counterpart',len(missing),'units',len(units),'cycles',[x for x in ordered if 'review_cycle' in x])
