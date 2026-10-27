#!/usr/bin/env python3
"""Assemble reviewable TX2 inventory; all equivalences remain proposed unless cited CLOSED."""
import json,pathlib,re,collections,hashlib,subprocess,time
O=pathlib.Path(__file__).resolve().parent;R=O.parents[1]
rows=json.load(open(O/'NBI2_mapped.json')); I=json.load(open(O/'NBI2_cohort_index.json'))
P=json.load(open(R/'evidence/replay-tops3-20261027/RPv_plan.json')); mapping=P['mapping'].copy()
for x in json.load(open(R/'evidence/replay-deployed2-20261027/RPx_plan.json'))['rows']:mapping[x['original']]=x['module']
C=set(json.load(open(R/'evidence/replay-deployed2-20261027/RPx_reachable-constants.json')))
closure=set(P['closures']['FJv_Top'])
files=subprocess.check_output(['git','ls-files','*.lean'],cwd=R,text=True).splitlines()
def module_for(f):
 path=f.removesuffix('.lean').replace('/','.')
 matches=[m for m in mapping if path.endswith('.'+m) or path==m]
 if matches:return max(matches,key=len)
 return pathlib.Path(f).stem

def locs(name):
 found=I.get(name,[]);out=[]
 for loc in found:
  mod=module_for(loc['file']);selected=mapping.get(mod,mod)
  # For renamed sources, their filename is itself the selected module.
  if mod in mapping and selected!=mod:continue
  if selected not in set(mapping.values()) and mod not in closure:continue
  out.append(dict(loc,module=selected))
 if not out:
  # Some source modules are library/generated imports outside planning repository contexts.
  out=[dict(x,module=module_for(x['file'])) for x in found if not x['file'].startswith('evidence/replay-')]
 return sorted(out,key=lambda x:(not x['file'].startswith('evidence/replay-deployed2'),not x['file'].startswith('evidence/replay-tops3'),x['file']))[:1]
def ref(name,kind='named definition'):
 assert name in C,name
 ll=locs(name)
 return dict(name=name,kind=kind,**(ll[0] if ll else {'module':'source locator unresolved','file':None,'line':None}))
# Source-aligned alternate names in the actual kernel closure; no equivalence is inferred from names.
alternate={
 'line_node':'R17FibrePointLineNodeActual.line_node',
 'circle_fold_with_inverses':'AspisR1.FIp_CircleQuery.circle',
 'line_fold_with_inverses':'AspisR1.SAQ_LineSource.line',
 'node_count':'AspisR1.Port4B_CountInstall.nodeCount',
 'verify_in_place':'AspisR1.MultiproofConeP6Verify.verify_in_place_owned',
 'batch_keys':'AspisR1.Port4B_KeyInstall.build',
 'sort_batch_keys':'AspisR1.Port4B_KeyInstall.packed',
 'batch_leaf':'AspisR1.Port4B_LeafCode.native',
 'slot_offset':'AspisR1.Port4B_SlotInstall.offset',
 'BatchedWeights::new':'AspisR1.Port3_NativePendingInstall.source',
}
# Helpers deliberately merged into these named parent definitions, rather than inventing separate counterparts.
parent={
 'batch_key_at':'AspisR1.Port3_NativeBatchBody.verifier.candidate.batch_tree',
 'same_batch_index':'AspisR1.Port3_NativeBatchBody.verifier.candidate.batch_tree',
 'same_batch_leaf':'AspisR1.Port3_NativeBatchBody.verifier.candidate.batch_tree',
 'finish_relation_round':'AspisR1.Port3_NativeFinishBody.verifier.finish_relation',
 'QueryGeometry::for_query':'AspisR1.Port3_NativeQueryBody.verifier.candidate.query_values',
 'basis_at':'AspisR1.Port3_NativeQueryBody.verifier.accumulate_batched_with_node',
 'accumulated_weight_at':'AspisR1.Port3_NativeQueryBody.verifier.accumulate_batched_with_node',
 'BatchedWeights::push':'AspisR1.Port3_NativeQueryBody.verifier.accumulate_batched_with_node',
 'power_limb_at':'AspisR1.Port3_NativeQueryBody.verifier.accumulate_batched_with_node',
 'residue_limb_at':'AspisR1.Port3_NativeQueryBody.verifier.accumulate_batched_with_node',
 'update_residue_row':'AspisR1.Port3_NativeQueryBody.verifier.accumulate_batched_with_node',
 'Arity::bits':'AspisR1.Port4B_CountInstall.nodeCount',
 'Arity::levels':'AspisR1.Port4B_CountInstall.nodeCount',
 'Arity::width':'AspisR1.Port4B_CountInstall.nodeCount',
 'index_at':'AspisR1.MultiproofConeP6Verify.verify_in_place_owned',
 'value_at':'AspisR1.MultiproofConeP6Verify.verify_in_place_owned',
 'root_matches':'AspisR1.MultiproofConeP6Verify.verify_in_place_owned',
 'occupied_binary_parent':'AspisR1.MultiproofConeP6Callbacks.parent',
 'sibling_binary_parent':'AspisR1.MultiproofConeP6Callbacks.parent',
 'well_formed':'AspisR1.MultiproofConeP6Verify.verify_in_place_owned',
 'private_leaf_hash_with_digest':'AspisR1.Port4B_LeafCode.native',
 'OwnedAccount::key':'AdapterRw.r1_pool_adapter.owned.authenticate_asq8_accounts',
 'OwnedAccount::owner':'AdapterRw.r1_pool_adapter.owned.require_readonly_account',
 'Variant::final_len':'AspisR1.CheckpointBytes4Ops.finalLen',
}
# Slots intentionally remain supplied by Uninstalled.adapter in this headline.
slot={
 'validate_verifier_policy_v1':15,'pool_v1_pair_forest_output_lane_v1':17,

 'decode_pool_v1_pair_forest_terminal_request_v1':23,
 'encode_pool_v1_pair_verified_afterstate_v1':24,
 'decode_verifier_registry_v1':31,'decode_verifier_registry_entry_v1':32,
 'decode_verifier_registry_v2':33,'decode_verifier_registry_entry_v2':34,
 'pool_program_id':45,'registry_program_id':46,
 'decode_master_box':48,'decode_checkpoint_box':49,'decode_lane_from_pool_release':50,
 'scan_proof_buffer':51,'reconstruct_asq8_statement':52,'emit_result':53,
 'VerifierRegistryV1::is_immutable':25,'VerifierRegistryV1::is_paused':26,
 'VerifierRegistryV2::is_immutable':27,'VerifierRegistryV2::is_paused':28,
 'VerifierRegistryEntryV2::is_active_at':29,'VerifierRegistryEntryV1::is_active_at':30,
}
# Units: lower IDs are predecessors (except internal cycles merged into the same unit).
units={
 'U00':('Release runtime leaves','S','Observer=None; trace is a release no-op; digest uses the SAME ordered parts and hashv state; map verifier errors exactly. Runtime/SHA256/allocator/SDK laws remain the named headline trust items.'),
 'U01':('Canonical arithmetic and byte carriers','M','M31/QM31/WideExact limbs <P; preserve little-endian limb order, decoded Result and all range/overflow checks. Pair every translated multiplication replacement with a named emitted-ok Lean theorem; never multiplication in Kani. Derive canonical intermediates and inversion input nonzero.'),
 'U02':('Atomic digest and payment codecs','M','Exact array/slice widths and canonical M31 digests; transfer and withdrawal header, version, reserved-byte, range and payment constraints; retain original bytes and every Result error.'),
 'U03':('Afterstate and live-snapshot codecs','M','Exact 688-byte candidate, fixed snapshot/frontier widths, canonical digests, next_pair_index bounds and preserved field/byte identity. No hash equality substituted for byte identity.'),
 'U04':('Registry and Pool account codecs','M','384-byte master,192-byte Pool checkpoint,128/256-byte registries and192/320-byte entries; both version/flag alternatives; canonical digests, immutable/unpaused policy and active-at-slot checks. This is the Pool checkpoint, not the1768-byte verifier checkpoint.'),
 'U05':('ASF8 statement and ASR8 result codecs','M','320-byte ASQ8,1880-byte ASF8, correct payment variant, common fields and candidate/frame identity; ASR8 validates against that SAME statement. Preserve full encoded bytes, not only semantic projections.'),
 'U06':('Private Dot terminal and public EbyKDot','M','CLOSED LPn private Dot::push: two private canonical Q operands, arbitrary four-u64 pre-state and actual wrap update. Public EbyKDot establishes checked_q and WideExact canonicality, count<4096 and SAME two accumulator writes; prove aggregate bound for finish, count<=4096, not just the local wrapping step.'),
 'U07':('Powers and four native query dots','M','gamma canonical from resume; powers29 on the same gamma; q length at least608 and each used 4/16-byte scalar canonical; four slots0..3,26 base products plus3 QM tails, EbyKDot term bound3, group raw sums fit u64.'),
 'U08':('Fast domain and transaction geometry','M','Query indices<2^18, range10..22; FibreIndex bounds; TABLE_A/B hash and index decomposition; all five x/y/z denominators nonzero; forward/backward inversion invariant with SAME vectors and start offsets.'),
 'U09':('Binary batch authentication','L','proof length57607, batch1/tree0..2, queries10..21 distinct<2^18, sort keys and deduplicate only equal leaves, at most12 occupied entries within MAX_BATCH16, exact slot count/padding and eighteen binary levels. Preserve ordered leaf/node digest calls, duplicate/error prefixes and three roots from SAME Prepared/proof.'),
 'U10':('Pending residues and accumulation','M','64 checkpoint weights canonical; rhs/power and folded value canonical; query index10..21; basis widths powers of2 up to64; residues at group boundaries<2^34 and four canonical products fit u64; terms advances once, flush at terms mod4=3, output weights equal source reductions.'),
 'U11':('Checkpoint reader and resume','L','SAME saved1768 bytes from TX1 under RuntimePersistence; header/tag/state1, next<=22, unique queries<2^18,64 canonical weights, all scalar reads bounded and final cursor1736. Recompute proof/public/checksum in source short-circuit order, against exact57607 proof and1880 public; tx2_common additionally proves next=10.'),
 'U12':('Weights construction and Pair kernels','L','S2,two folds, final_message length2048 and64 fields, semantic_alpha[10] and z[2] canonical; factor tensor shape5x5x4, points[3][10], low16/group12 tables, shared guard uses actual factor equality. Dot sizes64/16/4<4096; same final bytes and parts; one native iteration plus Lean induction for every tensor/group/dot loop.'),
 'U13':('Relation rounds and final dot','M','Two224-byte degree6 polynomials, two alphas and claim from same resume; relation lhs=claim/4 then Horner; invoke U12 on SAME final message/kappa; final dot64 canonical weights, next=22 and actual=rhs; preserve errors and marks(None).'),
 'U14':('Native query step and loop','L','Derive U07/U08/U10 domains from SAME Prepared,57607 proof, canonical admitted opening scalars, geometry.start=10 and current index<22. Check selected circle fold equals SAME q[672..800][u%4], line fold and accumulated node; native ONE step with arbitrary invariant state, then Lean induction to22.'),
 'U15':('Authenticated TX2 orchestration','M','parse_shape succeeds on original proof, then U11 resume next10; U09 batch1 before queries; U08 geometry10..22; U10 pending; U14 loop to22, end owned borrow before pending.finish, build SAME relation view then U13. No TX2 canonical_scan: establish canonical opening/round/final bytes from retained TX1 canonical scan or checked consumer decoders, not a stronger fresh assumption.'),
 'U16':('ASQ8 authentication and reconstruction','L','Seven distinct account keys; proof read-only nonsigner/nonexecutable, verifier checkpoint owner program/readonly/length1768; master/checkpoint/lane Pool-owned readonly; saved bumps and exact PDA seed order; authentic registry/policy/current slot; lane768 format/frontier/empty-root checks. Prove every U02-05 domain, scan58295 bytes into candidate688+proof57607, SAME request asset/nullifier lane and increment, reconstruct byte-identical ASF8.'),
 'U17':('ASR8 emission','M','U05 validates result against SAME accepted statement and encodes exact ASR8 length/magic; program::set_return_data receives those exact bytes after verifier acceptance. Return-data clear and subsequent set are ordered runtime effects, not unit-return success.'),
 'U18':('SDK second wrapper and program dispatch','L','Entry admits ASQ8 before borrowing; exactly7 accounts, seven bounded snapshots with original metadata/bytes and deferred errors, ordered guard release/owned cleanup; Clock::get actual success; clear return data before snapshots. Prove U16 validation -> encode1880 -> U15 on SAME proof suffix/checkpoint -> U17, retaining SDK/allocator laws and RuntimePersistence.'),
}
def unit(v):
 f=v['file'];n=v['name']
 if f.endswith(('lib.rs','pool_route.rs','trace.rs')):return 'U18' if n in ('process_r1_cost_probe_instruction','admitted') else 'U00'
 if f.startswith('crates/aspis-core/src/field') or f.endswith('r0/scalar.rs'):return 'U01'
 if f.endswith('r0/heap.rs'):return 'U00'
 if f.endswith('atomic_statement.rs') or f.endswith('payment_relation.rs'):return 'U02'
 if f.endswith(('pair_terminal.rs','pair_tree_profile.rs')):return 'U03'
 if f.endswith(('format.rs','pair_forest_accounts.rs','verifier_registry.rs')):return 'U04'
 if f.endswith('pair_forest_terminal.rs'):return 'U05'
 if f.endswith('fast_pairing.rs'):return 'U06'
 if f.endswith('fast_dots.rs'):return 'U07'
 if f.endswith(('fast_domain.rs','r0/domain.rs')):return 'U08'
 if f.endswith(('multiproof.rs','compact.rs','state_only_private_merkle.rs')):return 'U09'
 if f.endswith(('state_only_prefix.rs','weights.rs')):return 'U07' if n in ('powers','field') else 'U12'
 if f.endswith('candidate.rs'):
  return 'U15' if n in ('tx2_authenticated','tx2_common','parse_shape') else 'U14' if n in ('query_values','query_loop') else 'U09'
 if f.endswith('verifier.rs'):
  if n in ('mark',):return 'U00'
  if n=='checkpoint_size':return 'U01'
  if n.startswith('Reader') or n.startswith(('validate_checkpoint','read_checkpoint')) or n=='resume':return 'U11'
  if n.startswith('QueryGeometry') or n=='batch_prefix_products':return 'U08'
  if n in ('circle_fold_with_inverses','line_fold_with_inverses'):return 'U14'
  if n.startswith(('finish','polynomial')):return 'U13'
  return 'U10'
 if f.endswith('transport.rs'):return 'U01'
 if f.endswith('r1_pool_adapter.rs'):
  if n=='emit_result':return 'U17'
  if n=='process':return 'U18'
  return 'U16'
 if f.endswith('r1_pool_adapter_owned.rs'):
  return 'U18' if n in ('stage2','stage2_owned','snapshot') else 'U16'
 raise Exception(v['id'])
for v in rows:
 v['bridge_unit']=unit(v);v['estimate']=units[v['bridge_unit']][1]
 defs=[]
 for old in v['cohort_definitions']:
  defs.append(ref(old['name']))
 if v['name']=='encode_pool_v1_pair_forest_terminal_statement_v1':defs.append(ref('AspisS6CurrentCodecInstallation.encode','installed op22 concrete serialization'))
 if v['name'] in alternate:defs.append(ref(alternate[v['name']],'source-shaped model with different name'))
 v['cohort_definitions']=list({x['name']:x for x in defs}.values())
 v['cohort_status']='named counterpart in replayed kernel closure' if defs else 'no cohort counterpart'
 v['model_context']= [ref(parent[v['name']],'parent/context, no separate counterpart')] if v['name'] in parent else []
 v['abstract_adapter_slot']=slot.get(v['name'])
 v['modelling_gap']= bool(v['abstract_adapter_slot']) or v['name'] in ('emit_result','process_r1_cost_probe_instruction','process')
 v['gap_note']= 'Native body not concretely installed here; AdapterRw.Ops.op'+str(v['abstract_adapter_slot'])+' remains the boundary supplied by missing.adapter.' if v['abstract_adapter_slot'] else ('Entrypoint/return-data effect association remains at runtime/extraction boundary.' if v['modelling_gap'] else None)
 v['callee_bridges']=sorted({unit(next(x for x in rows if x['id']==h)) for c in v['calls'] if c['resolution'] not in ('disabled release cfg',) for h in c['targets'] if h!=v['id']})
 v['caller_domain_to_establish']=units[v['bridge_unit']][2]
 if v['name']=='field' and v['file'].endswith('weights.rs'):v['caller_domain_to_establish']='i>=0, 32*(i+1)<=bytes.len(), exactly eight canonical little-endian M31 words in bytes[32*i..32*(i+1)]; preserve this actual slice and Result.'
 if v['name']=='checkpoint_size':v['caller_domain_to_establish']='Variant::S2; folds=2, final_len=64 and fixed checksum/header sizing imply result1768. No assumption about checkpoint bytes is required to compute its length.'
 if v['name']=='powers':v['caller_domain_to_establish']='Canonical WideExact x; reached N=4,7,29. ONE multiply step with output[j]=x^j invariant, then Lean induction. No restriction on unrelated query inputs.'
 if v['name'].startswith('FibreIndex::'):v['caller_domain_to_establish']='Constructor checks index<262144; get returns SAME checked index. Model macro expansion explicitly, no arbitrary unchecked index.'
 if v['bridge_unit']!='U00' and any(c['name'] in ('digest','hashv','create_program_address','set_return_data') and c['resolution']!='disabled release cfg' for c in v['calls']):v['callee_bridges']=sorted(set(v['callee_bridges']+['U00']))
 v['callee_domains']=[{'function':h,'unit':unit(next(x for x in rows if x['id']==h)),'obligation':'Establish the concrete callee function domain, as recorded on that function row, using this same call-site arguments/state; never assume a separate successful call.'} for h in sorted({h for c in v['calls'] for h in c['targets']})]

# Capture propagated decoder/result helpers that have no named model under an abstract ancestor.
for v in rows:
 if not v['cohort_definitions'] and not v['model_context'] and v['bridge_unit'] in ('U04','U05','U16','U17'):
  v['modelling_gap']=True
  if not v['gap_note']:v['gap_note']='Reached helper under an abstract adapter boundary; no separate executable counterpart occurs in the adopted kernel dependency set. Prove inside the enclosing codec/authentication/emission bridge.'
# The thirteen CLOSED opaque leaf boundary list; only Dot::push is reached after saved preparation.
leafs=[('sampler::low_base_p_digits','leaf-sampler1-20261027/LPk_LEAF.md'),('verifier::echeck','leaf-p6-10-20261027/LPl_echeck_LEAF.md'),('r1_wire::validate_record_fields','leaf-p6-10-20261027/LPl_validate_record_fields_LEAF.md'),('compact::check_values','leaf-p6-10-20261027/LPl_check_values_LEAF.md'),('compact::expand_values','leaf-p6-12-20261027/LPn_expand_values_LEAF.md'),('ValidatedRecord::decode_k','leaf-p6-12-20261027/LPn_decode_k_LEAF.md'),('r1_semantic::claims','leaf-p6-12-20261027/LPn_claims_LEAF.md'),('canonical::Dot::push','leaf-p6-12-20261027/LPn_Dot_push_LEAF.md'),('candidate::wide_view','leaf-p6-13-20261027/LPo_wide_view_LEAF.md'),('semantic_boundary','leaf-p6-13-20261027/LPo_semantic_boundary_LEAF.md'),('circle_sample','leaf-p6-14-20261027/LPp_circle_sample_LEAF.md'),('verifier::checkpoint','leaf-p6-11-20261027/LPm_checkpoint_LEAF.md'),('verifier::prepared_claim','leaf-p6-18-20261027/LPt_prepared_claim_LEAF.md')]
# Callee bridge graph is explicit and includes all repository functions and separate external call sites.
byid={v['id']:v for v in rows};urows=[]
for k,(title,size,domain) in units.items():
 members=[v['id'] for v in rows if v['bridge_unit']==k]
 deps=sorted({d for v in rows if v['bridge_unit']==k for d in v['callee_bridges'] if d!=k})
 urows.append(dict(id=k,title=title,estimate=size,domain=domain,members=members,callee_bridges=deps,status='proposed; no enclosing bridge proved by this inventory'))
# Topological order independent of the display IDs; report any cycle rather than hiding one.
ordered=[];pending={u['id']:u for u in urows}
while pending:
 ready=[k for k,v in pending.items() if all(d in ordered for d in v['callee_bridges'])]
 if not ready:raise Exception('unit cycle: '+str({k:v['callee_bridges'] for k,v in pending.items()}))
 for k in sorted(ready):ordered.append(k);pending.pop(k)
urows=sorted(urows,key=lambda u:ordered.index(u['id']))
data={'schema_version':1,'headline':'AspisR1.RPx_Deployed.deployed','source_revision':'4bb3b3f51e16b4525f1d10336e2b0bcbbd775387','inventory_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),'scope':'Accepted Pool-adapter ASQ8 TX2 verifier invocation; repository functions down to CLOSED opaque leaves; closures bundled with parents; external SDK/std/syscall boundaries listed at call sites','features':{'r1_program':['custom-heap','pool-adapter','private-leaf-salts'],'r1_library':['optimized-terminal','program-build','private-leaf-salts'],'excluded':['test','kani','prover','audit-eight-way','cu-profiling','r0-op-count','r0-r91-audit','r0-e4-reference'],'deployment_ids':'default/devnet constants are macro data, not distinct functions; this invocation does not execute Pool settlement after ASR8'},'body_hash_rule':'SHA256 of exact frozen source bytes from opening { through closing }; line and byte offsets are zero-based bytes / one-based lines. Macro methods hash template and cite invocation. Disabled branches remain in full body hash.','method_limits':['Tree-sitter call-site inventory with explicit source/type/feature resolution, not compiler reachability or a proof of source correspondence.','Field method call targets conservatively list canonical M31/CM31/QM31/WideExact alternatives; canonical carrier discharge is explicitly required by bridge units.','Runtime-branch pruning specializes S2/two-fold, binary Arity::Two and pool-adapter; generic unused branches are retained in body hashes but excluded from bridge reachability.','No claim that each same-suffix cohort candidate is already associated with native execution; the listed bridge units are obligations.'], 'closed_leaves':[dict(function=n,evidence='evidence/'+p,reached_in_tx2=n=='canonical::Dot::push',status='CLOSED local domain per cited packet; not an enclosing/headline bridge') for n,p in leafs],'bridge_units_bottom_up':urows,'functions':rows,'counts':{'functions':len(rows),'files':len({v['file'] for v in rows}),'no_separate_counterpart':sum(not v['cohort_definitions'] for v in rows),'gap_rows':sum(v['modelling_gap'] for v in rows),'lean_attempts':0,'kani_runs':0,'rust_runs':0},'assumptions':'No premise/trust-item/metric/carrier/quantifier changed or removed. L154 statement parameter retained. Narrowed D188, frozen3 and RuntimePersistence retained.'}
(O/'NBI2_INVENTORY.json').write_text(json.dumps(data,indent=2)+'\n')
print(data['counts']);print('bottom up',ordered)
