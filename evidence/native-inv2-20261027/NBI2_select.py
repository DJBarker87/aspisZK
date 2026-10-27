#!/usr/bin/env python3
import json,pathlib,re,collections
O=pathlib.Path(__file__).resolve().parent
S=json.load(open(O/'NBI2_scan.json')); F=S['functions']
FEATURES={'pool-adapter','custom-heap','private-leaf-salts','program-build','optimized-terminal','r0','pool-v1-kernel'}
def cfg_expr(x):
 x=x.strip()
 if x.startswith(('all(', 'any(', 'not(')):
  op,rest=x.split('(',1);rest=rest[:-1];args=[];depth=0;start=0
  for i,c in enumerate(rest):
   if c=='(':depth+=1
   if c==')':depth-=1
   if c==',' and depth==0:args.append(rest[start:i]);start=i+1
  args.append(rest[start:]);vals=[cfg_expr(a) for a in args if a.strip()]
  return all(vals) if op=='all' else any(vals) if op=='any' else not vals[0]
 m=re.fullmatch(r'feature\s*=\s*"([^"]+)"',x)
 if m:return m[1] in FEATURES
 if 'target_os' in x:return '"solana"' in x
 return False

def active(attrs):
 return all(cfg_expr(a[6:-2]) for a in attrs if a.startswith('#[cfg('))
def eligible(v):return active(v['attributes'])
F={k:v for k,v in F.items() if eligible(v)}
byname=collections.defaultdict(list)
for k,v in F.items():byname[v['short_name']].append(k)
sel=set(); reasons={}; exclusions=[]
def add(file,names,why='explicit source path'):
 for name in names.split():
  hits=[k for k,v in F.items() if v['file'].endswith(file) and v['name']==name]
  assert len(hits)==1,(file,name,hits)
  sel.add(hits[0]);reasons[hits[0]]=why
add('programs/r1-cost-probe/src/lib.rs','process_r1_cost_probe_instruction SolanaDigest::digest observer error')
add('programs/r1-cost-probe/src/pool_route.rs','admitted')
add('programs/r1-cost-probe/src/r1_pool_adapter_owned.rs','stage2 stage2_owned snapshot OwnedAccount::key OwnedAccount::owner OwnedAccount::data OwnedAccount::data_len require_readonly_buffer require_readonly_account require_verifier_checkpoint require_distinct_accounts authenticate_invariant_release_registry authenticate_asq8_accounts validate_asq8')
add('programs/r1-cost-probe/src/r1_pool_adapter.rs','pool_program_id registry_program_id process readonly_meta_ok readonly_buffer_meta_ok decode_master_box decode_checkpoint_box decode_lane_from_pool_release scan_proof_buffer asq8_common transfer_statement_box withdrawal_statement_box reconstruct_asq8_statement emit_result')
add('crates/aspis-r1-cost-probe/src/candidate.rs','tx2_authenticated tx2_common parse_shape batch_merkle batch_merkle_values batch_tree batch_keys sort_batch_keys batch_key_at batch_leaf same_batch_index same_batch_leaf opening slot query_values query_loop')
add('crates/aspis-r1-cost-probe/src/verifier.rs','resume checkpoint_size mark Reader<\'a>::raw Reader<\'a>::e Reader<\'a>::k validate_checkpoint_queries read_checkpoint_weights read_checkpoint_semantic_alpha QueryGeometry::for_range QueryGeometry::for_query batch_prefix_products BatchedWeights::new BatchedWeights::push BatchedWeights::value BatchedWeights::finish residue_limb_at power_limb_at update_residue_row circle_fold_with_inverses line_fold_with_inverses accumulate_batched_with_node basis_at accumulated_weight_at polynomial finish_relation_round finish_query_dot finish_relation')
add('crates/aspis-r1-cost-probe/src/weights.rs','powers double field Weights::new Weights::box_from_parts Weights::pair Weights::tensor Weights::scalar_factor process_regular_kinds process_kind push_byte_products shared_two_point_guard shared_partials shared_high partial_dot high_dot grouped_inactive_pair s2_grouped_inactive_pair factored_s2_libra_weights')
add('crates/aspis-r1-cost-probe/src/fast_dots.rs','four_dots four_dots_one')
add('crates/aspis-r1-cost-probe/src/fast_pairing.rs','EbyKDot::new EbyKDot::push EbyKDot::finish checked_q limbs_of canonical::Q::from_limbs canonical::Q::from_wide canonical::Q::limbs canonical::Dot::new canonical::Dot::push canonical::Dot::finish canonical::reduce')
add('crates/aspis-statement/src/pool_v1/payment_relation.rs','encode_pool_v1_private_transfer_public_v1 encode_pool_v1_withdrawal_public_v1')
add('crates/aspis-r1-cost-probe/src/multiproof.rs','Arity::bits Arity::width Arity::levels')
add('crates/aspis-core/src/r0/domain.rs','FibreIndex::new FibreIndex::get')
add('crates/aspis-core/src/r0/scalar.rs','WideExact::from_m31')
# Closed leaves are terminals; calls inside their body remain listed but not recursively expanded.
CLOSED={'canonical::Dot::push':('LPn','evidence/leaf-p6-12-20261027/LPn_Dot_push_LEAF.md')}
# Primitive field operations are their own bridge units; include their real dependency closure.
add('crates/aspis-core/src/field/wide_exact.rs','WideExact::new WideExact::c0 WideExact::c1 WideExact::from_qm31 WideExact::add WideExact::sub WideExact::mul WideExact::mul_qm31 WideExact::mul_m31 WideExact::from_limbs WideExact::to_limbs WideExact::from_le_bytes WideExact::to_le_bytes canonical_qm31 mul_u')
add('crates/aspis-core/src/field.rs','QM31::from_cm31 QM31::square CM31::new reduce_u64 square_n M31::add M31::sub M31::mul M31::double M31::reduce_u64 M31::from_le_bytes M31::to_le_bytes M31::inv CM31::add CM31::sub CM31::mul CM31::mul_m31 CM31::double CM31::from_le_bytes CM31::write_le_bytes QM31::add QM31::sub QM31::mul QM31::mul_m31 QM31::from_le_bytes QM31::write_le_bytes mul_by_r')
# Dead branches in exact adopted S2/release specialization.
SKIP={'stage1','stage1_owned','first','first_decoded','lifecycle_init','lifecycle_write','lifecycle_finalize','canonical_scan','tx1','tx2','prepare','prepared_claim','twofold_libra_weights','raw','dual_raw','dense_point_pair','eight_way_proof_bytes','mark_profile'}
STD=set('Some Ok Err None new with_capacity from_le_bytes to_le_bytes from from_fn try_from try_into into as_ref as_mut as_deref_mut len is_empty first get get_mut copied clone unwrap expect ok_or ok_or_else map map_err and_then is_some is_none iter iter_mut enumerate rev chunks_exact chunks chunks_mut contains any all fold collect extend_from_slice push pop insert resize truncate clear split_at split_at_mut copy_from_slice starts_with then_some checked_add checked_sub checked_mul wrapping_add wrapping_sub wrapping_mul wrapping_shr wrapping_shl rotate_left rotate_right to_vec to_bytes new_from_array create_program_address find_program_address try_borrow_data try_borrow_mut_data set_return_data digest hashv sort_unstable sort_unstable_by_key is_power_of_two trailing_zeros leading_zeros min max next sum zip cmp swap split_first split_first_mut get_unchecked write read drop take as_slice as_mut_slice slice_from_raw_parts'.split())
# Manual method dispatch for non-field mutable/domain carriers.
METHOD={
 'is_immutable':'verifier_registry.rs','is_paused':'verifier_registry.rs','is_active_at':'verifier_registry.rs',
 'common':'pair_forest_terminal.rs','transition_kind':'pair_forest_terminal.rs','nullifier':'pair_forest_terminal.rs',
 'folds':'transport.rs','final_len':'transport.rs','tag':'transport.rs',
 'for_query':'verifier.rs','finish':'fast_pairing.rs','tensor':'weights.rs','pair':'weights.rs','scalar_factor':'weights.rs',
 'data':'r1_pool_adapter_owned.rs','data_len':'r1_pool_adapter_owned.rs','key':'r1_pool_adapter_owned.rs','owner':'r1_pool_adapter_owned.rs'}
module_alias={'E':'field/wide_exact.rs','WideExact':'field/wide_exact.rs','K':'field.rs','M31':'field.rs','QM31':'field.rs','CM31':'field.rs','Self':None,'Variant':'transport.rs','Weights':'weights.rs','Reader':'verifier.rs','QueryGeometry':'verifier.rs','BatchedWeights':'verifier.rs','EbyKDot':'fast_pairing.rs','FibreIndex':'r0/domain.rs'}
def resolve(k,c):
 v=F[k];name=c['name'];sy=c['syntax'];recv=c.get('receiver','');same=[h for h in byname[name] if F[h]['file']==v['file']]
 if sy in v.get('local_closures',[]):return [],'local closure body bundled with caller'
 if not active(c.get('cfg',[])):return [],'disabled release cfg'
 if name in ('M31','Q','Self','PrivateTransfer','Withdrawal','Afterstate','LaneTransition','Payment','Account','Query','Merkle'):return [],'constructor (no function body)'
 if name in ('bits','levels','width') and (recv in ('arity','self')) and v['file'].endswith('multiproof.rs'):return [h for h in byname[name] if F[h]['file'].endswith('multiproof.rs')],'multiproof Arity receiver'
 if name=='Snapshot':return [],'constructor (no function body)'
 if name=='statement_points':return [h for h in byname[name] if F[h]['file'].endswith('state_only_prefix.rs')],'state-only r0 module helper'
 if name=='has_no_retirement_slot':return [h for h in byname[name] if F[h]['file'].endswith('verifier_registry.rs')],'version-specific registry receiver'
 if name in ('e','k','raw') and recv in ('r','reader'):
  return [h for h in byname[name] if F[h]['file'].endswith('verifier.rs') and 'Reader' in F[h]['name']],'checkpoint Reader receiver'
 if name=='value' and recv=='self' and 'BatchedWeights::' in v['name']:return [h for h in byname[name] if F[h]['file'].endswith('verifier.rs') and F[h]['name']=='BatchedWeights::value'],'BatchedWeights receiver'
 if name=='from_limbs' and sy=='canonical::Q::from_limbs':return [h for h in byname[name] if F[h]['file'].endswith('fast_pairing.rs') and F[h]['name']=='canonical::Q::from_limbs'],'private Q constructor'
 if name=='limbs' and 'finish()' in recv:return [h for h in byname[name] if F[h]['file'].endswith('fast_pairing.rs') and F[h]['name']=='canonical::Q::limbs'],'private finished Q'
 if name=='mul_re3':return [h for h in byname[name] if F[h]['file'].endswith('field/wide_exact.rs')],'WideExact receiver'
 if name=='square':return [h for h in byname[name] if F[h]['file'].endswith('field.rs') and F[h]['name']=='QM31::square'],'QM31 Libra powers'
 if name in ('step_by','chunks_exact_mut','windows','fill','try_reserve_exact','sol_log_compute_units','sol_log_64','size_of','black_box','id','f','from_m31'):return [],'standard/runtime/closure boundary'
 if name=='get' and recv=='u' and v['file'].endswith('fast_domain.rs'):return [h for h in byname[name] if F[h]['file'].endswith('r0/domain.rs') and F[h]['name']=='FibreIndex::get'],'checked FibreIndex projection'
 if name=='parent_with_digest' and v['file'].endswith('multiproof.rs'):return [],'excluded Arity::Eight branch'
 if name=='from_m31' and sy=='E::from_m31':return [h for h in byname[name] if F[h]['file'].endswith('r0/scalar.rs') and F[h]['name']=='WideExact::from_m31'],'CodeField WideExact embedding'
 if name=='kpowers' and v['file'].endswith('weights.rs'):return [],'excluded folds=1 branch'
 if v['name']=='canonical::Dot::push' and name=='raw':return [],'inside CLOSED terminal: canonical::Q::raw; LPn_Dot_push_LEAF.md'
 if recv and name=='first':return [],'standard slice primitive'
 if name in SKIP:return [],'excluded S2/release branch'
 if name in ('value','mark') and sy.startswith('crate::trace'):return [h for h in byname[name] if F[h]['file'].endswith('/trace.rs')],'release no-op trace'
 if recv:
  if name in ('push','finish') and (recv in ('dot','pair','high','tail') or (v['file'].endswith('fast_pairing.rs') and recv.startswith('self.c'))):
   owner='canonical::Dot' if recv.startswith('self.c') else 'EbyKDot';return [h for h in byname[name] if F[h]['file'].endswith('fast_pairing.rs') and F[h]['name']==owner+'::'+name],'typed dot receiver'
  if name in ('data','data_len','key','owner') and '/r1_pool_adapter' in v['file']:return [h for h in byname[name] if F[h]['file'].endswith('r1_pool_adapter_owned.rs')],'owned snapshot receiver'
  if name in ('push','finish','value') and recv in ('weights','pending') and v['file'].endswith(('verifier.rs','candidate.rs')):return [h for h in byname[name] if F[h]['file'].endswith('verifier.rs') and F[h]['name']=='BatchedWeights::'+name],'batched weights receiver'
  if name in METHOD and name not in ('finish',):
   hs=[h for h in byname[name] if F[h]['file'].endswith('/'+METHOD[name])];return hs,'typed receiver branch union'
  # Arithmetic receivers may have multiple field types; exact calls documented as typed-port obligations.
  if name in ('add','sub','mul','mul_m31','mul_qm31','double','inv','c0','c1','to_limbs','to_le_bytes','write_le_bytes'):
   hs=[h for h in sel if F[h]['short_name']==name and F[h]['file'].startswith('crates/aspis-core/src/field')];return hs,'field type conservative union (bridge must resolve carrier)'
 if '::' in sy:
  parts=sy.split('::');owner=parts[-2];base=module_alias.get(owner,'?')
  if owner=='Self':
   typ=v['name'].rsplit('::',1)[0];hs=[h for h in same if F[h]['name']==typ+'::'+name]
   if hs:return hs,'Self dispatch'
  if base and base!='?':
   aliases={'E':'WideExact','K':'QM31'};typ=aliases.get(owner,owner)
   hs=[h for h in byname[name] if F[h]['file'].endswith(base) and (F[h]['name'].split('::')[-2:]==[typ,name] or typ in ('Reader','FibreIndex'))]
   if hs:return hs,'explicit type dispatch'
  # Module-qualified free function.
  hs=[h for h in byname[name] if F[h]['file'].endswith('/'+owner+'.rs')]
  if hs:return hs,'explicit module dispatch'
 if not recv:
  local=[h for h in same if F[h]['name']==v['name']+'::'+name]
  if local:return local,'nested local function'
  # Local helper, including outer module import in owned adapter.
  hs=[h for h in same if '::' not in F[h]['name']]
  if hs:return hs,'same module helper'
  if '/r1_pool_adapter_owned.rs' in v['file']:
   hs=[h for h in byname[name] if F[h]['file'].endswith('/r1_pool_adapter.rs')]
   if hs:return hs,'outer adapter import'
  hs=[h for h in byname[name] if h in sel]
  if len(hs)==1:return hs,'selected unique source helper'
  hs=[h for h in byname[name] if F[h]['file'].startswith(('crates/aspis-statement/','crates/aspis-r1-cost-probe/','crates/aspis-core/'))]
  if len(hs)==1:return hs,'unique crate function'
 if name in STD:return [],'standard/runtime/closure boundary'
 return [],'unresolved native dispatch'
for _ in range(15):
 old=len(sel)
 for k in list(sel):
  if F[k]['name'] in CLOSED:continue
  for c in F[k]['calls']:
   hs,why=resolve(k,c)
   for h in hs:
    if h not in sel:sel.add(h);reasons[h]=k+' -> '+c['syntax']+' ('+why+')'
 if len(sel)==old:break
rows=[]
for k in sorted(sel):
 v=F[k].copy();v['selection_reason']=reasons.get(k,'discovered call');v['closed_leaf']=CLOSED.get(v['name']);v['calls']=[dict(c,targets=resolve(k,c)[0],resolution=resolve(k,c)[1]) for c in v['calls']];rows.append(v)
(O/'NBI2_selected.json').write_text(json.dumps(rows,indent=2)+'\n')
print('selected',len(rows),'files',len(set(v['file'] for v in rows)))
for v in rows:
 u=sorted(set(c['syntax'] for c in v['calls'] if c['resolution']=='unresolved native dispatch'))
 if u: print(v['file'].split('/')[-1]+'::'+v['name'],u)
