import json,re,pathlib,collections,hashlib,subprocess
E=pathlib.Path(__file__).parent
b=json.load(open(E/'NCS_BODY_HASHES.json')); bodies={x['id']:x for x in b['bodies']}
inv2=json.load(open('evidence/native-inv2-20261027/NBI2_INVENTORY.json'))['functions'];inv1=json.load(open('evidence/native-inv1-20261027/NBI1_INVENTORY.json'))['functions']
# Exact body hashes resolve inventory IDs, including overloaded methods and duplicate cfg alternatives.
byhash=collections.defaultdict(list)
for x in bodies.values():byhash[(x['file'],x['body_sha256'])].append(x['id'])
canon={};edges=collections.defaultdict(set);unresolved=collections.defaultdict(list)
for x in inv2+inv1:
 ids=byhash[(x['file'],x['body_sha256'])]
 if len(ids)==1:canon[x['id']]=ids[0]
for x in inv2+inv1:
 key=canon.get(x['id'])
 if not key:continue
 for c in x.get('callees',x.get('calls',[])):
  ts=c.get('targets',[])
  for t in ts:
   if t in canon:edges[key].add(canon[t])
   else:unresolved[key].append(dict(call=c,target=t,reason='target absent from pinned body map'))
  if not ts:unresolved[key].append(dict(call=c,reason='inventory external/closure/dynamic boundary'))
rows=json.load(open(E/'NCS_CREDIT_INVENTORY.json'))['rows']
# Resolve documented aliases; keep exact type/file anchors for ambiguous short names.
alias={'verifier::echeck':'crates/aspis-r1-cost-probe/src/verifier.rs::echeck','r1_wire::validate_record_fields':'crates/aspis-r1-cost-probe/src/r1_wire.rs::validate_record_fields','ValidatedRecord::decode_k':'crates/aspis-r1-cost-probe/src/r1_wire.rs::ValidatedRecord<\'a>::decode_k','canonical::Dot::push':'crates/aspis-r1-cost-probe/src/fast_pairing.rs::canonical::Dot::push','semantic_boundary':'crates/aspis-r1-cost-probe/src/r1_semantic.rs::semantic_boundary','circle_sample':'crates/aspis-r1-cost-probe/src/sampler.rs::circle_sample','sampler::low_base_p_digits':'crates/aspis-r1-cost-probe/src/sampler.rs::low_base_p_digits','powers':'crates/aspis-r1-cost-probe/src/weights.rs::powers','error':'programs/r1-cost-probe/src/lib.rs::error','observer':'programs/r1-cost-probe/src/lib.rs::observer','mark':'crates/aspis-r1-cost-probe/src/verifier.rs::mark','value':'crates/aspis-r1-cost-probe/src/trace.rs::value','SolanaDigest::digest':'programs/r1-cost-probe/src/lib.rs::SolanaDigest::digest','inactive serializer statement5':'crates/aspis-r1-cost-probe/src/verifier.rs::Prepared::new','ASF8 encode statement':'crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::encode_pool_v1_pair_forest_terminal_statement_v1','ASF8 validate statement':'crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::validate_pool_v1_pair_forest_terminal_statement_v1'}
for original in ['LPa_K004','LPl_K015','LPg_K011','LPg_K012','LPh_K018','LPh_K019','LPh_K020','LPh_K021','LPn_K001']:
 alias[original]='crates/aspis-r1-cost-probe/src/compact.rs::expand_values'
alias['LPn_K010']="crates/aspis-r1-cost-probe/src/r1_wire.rs::ValidatedRecord<'a>::decode_k"
alias['LPa_K015']='crates/aspis-r1-cost-probe/src/candidate.rs::wide_view'
for original in ['LPi_K005','LPi_K006','LPi_K007','LPi_K008','LPi_K009','LPi_K010']:alias[original]='crates/aspis-core/src/field.rs::QM31::write_le_bytes'
alias['NBH_K029']='crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::encode_pool_v1_pair_forest_terminal_statement_v1'
for original in ['LPe_K015','LPe_K018','LPm_K001','LPe_K019','LPe_K016']:alias[original]='crates/aspis-r1-cost-probe/src/verifier.rs::checkpoint'
for original in ['LPb_K016','LPe_K005']:alias[original]='crates/aspis-r1-cost-probe/src/verifier.rs::prepared_claim'
def norm(s):return re.sub(r"<[^>]*>",'',s).replace('r1_wire::','').replace('canonical::','').replace('r1_semantic::','')
def roots(m):
 m=m.replace('`','');m=alias.get(m,m)
 if m in bodies:return [m]
 if m in canon:return [canon[m]]
 if '.rs::'in m:
  f,n=m.split('.rs::',1);return [k for k,x in bodies.items()if x['file']==f+'.rs' and norm(x['name'])==norm(n)]
 # Qualified module names select file stem, then method owner.
 parts=m.split('::');out=[]
 for k,x in bodies.items():
  if not x['file'].startswith(('crates/aspis-core/','crates/aspis-r1-cost-probe/','crates/aspis-statement/','programs/r1-cost-probe/')):continue
  if norm(x['name'])==norm(m):out.append(k)
  elif len(parts)>1 and pathlib.Path(x['file']).stem==parts[0]and norm(x['name'])==norm('::'.join(parts[1:])):out.append(k)
 return out
out=[]
for r in rows:
 rr=roots(r['member']);seen=set();todo=list(rr)
 while todo:
  k=todo.pop()
  if k in seen:continue
  seen.add(k);todo.extend(edges[k]-seen)
 differences=[];unknown=[]
 for k in sorted(seen):
  x=bodies[k];a=x['configurations']['library-default'];z=x['configurations']['library-deployed']
  if a['sha256']!=z['sha256']:differences.append(k)
  if a['unknown']or z['unknown']:unknown.append(k)
 out.append(dict(**r,roots=rr,reached_inventory_bodies=sorted(seen),differing_library_bodies=differences,cfg_unknown_bodies=unknown,unresolved_edges={k:unresolved[k]for k in sorted(seen)if unresolved[k]}))
# Tables and machine ledgers sometimes spell the same member with/without its file stem.
# Merge only identical resolved roots within a packet; distinct restored harness properties stay separate.
merged={}
for r in out:
 key=(r['packet'],tuple(r['roots'])) if r['packet'] not in ('KMX','KMZ','P6') else (r['id'],)
 if key not in merged:
  r['id']=r['id'].replace('`','');r['member']=r['member'].replace('`','');r['alias_credit_ids']=[];merged[key]=r
 else:
  q=merged[key];q['alias_credit_ids'].append(r['id']);q['sources']+=r['sources'];q['detail']+=r['detail']
  if 'CONDITIONAL'in r['credited_status']:q['credited_status']='CLOSED-CONDITIONAL'
out=sorted(merged.values(),key=lambda r:r['id'])
(E/'NCS_ASSOCIATIONS.json').write_text(json.dumps(dict(rows=out,method='Conservative union of TX1/TX2 inventory edges, exact frozen body SHA association. Edges stop at documented opaque/external boundaries; unresolved edges retained, not dynamically certified harness closure.'),indent=2)+'\n')
print('rows',len(out),'unmapped',[(r['packet'],r['member'])for r in out if not r['roots']]);print('differences',[(r['id'],r['differing_library_bodies'])for r in out if r['differing_library_bodies']]);print('cfg unknown',sum(bool(r['cfg_unknown_bodies'])for r in out))
