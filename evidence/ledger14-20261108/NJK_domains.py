from pathlib import Path
import json,lzma
E=Path(__file__).resolve().parent
b=json.loads(lzma.decompress((E.parent/'ledger13-20261107/NIU_LEDGER.json.xz').read_bytes()));by={r['row']:r for r in b['rows']};byfun={}
for r in b['rows']:byfun.setdefault(r['function'],[]).append(r)
c=json.loads((E/'NJK_CANDIDATE_REVIEW.json').read_text());cm={r['function']:r for r in c['rows']if r['admissible']};out=[]
def domain(row,f):
 if row=='TX2:115':
  if f.endswith('::Weights::pair'):return 'NJF_Root.finish SAME execution.2.2 Bound; NIT_PairDomain.caller at actual NEW Ok return; full PairPort on same collected Result. FinishInput.Domain retained, not asserted discharged at upstream caller.'
  if f.endswith('::Weights::new'):return 'NIG_FinishInput.Domain gives S2/canonical semantic_alpha and z. NJF_FinishObserved.source internally applies CLOSED new at same p.variant/p.semantic_alpha/p.z, preserving every Result arm before entering pair.'
  if f.endswith('::finish_relation_round'):return 'Same final_message, alpha index0/1 and claim from actual preceding result; NJF_FinishInstantiation.source + FinishObserved.source produce event Clause/Inputs. Closed round result supplied at entered arguments, first error/abort prevents suffix.'
  if f.endswith('::finish_query_dot'):return 'Same final_message and actual canonical64 pair output, final source accumulator/claim; original final-next/actual=rhs constraints retained by SAME FinishInput.Domain and actual source branches; complete Result/marks kept.'
  return 'Complete source Clause/Inputs inside NJF_FinishObserved.source at SAME entered event. Variant::folds specializes actual S2; trace::value and mark use deployed release definitions/None. No separate endpoint/success premise.'
 if row=='TX2:129':
  if '/field' in f:return 'NIT_PairDomain from SAME NEW return; NJF_RegularInstantiation and RegularContinuation supply canonical actual operands/replies and full child post/frame; each field product is paired with emitted Lean mul law, not Kani arithmetic.'
  if f.endswith('::filled'):return 'CLOSED TX2:045/NIG_FilledCoverage + NHM_Filled64 on exact length64 and canonical zero; same actual allocator outcome realization r. Err returns Allocation; Ok supplies zero64 regular invariant. No arbitrary reserve Bool is assumed.'
  return 'NJF_PairInstantiation + AllocatorInstantiation + RegularInstantiation/RegularContinuation substitute CLOSED result at SAME decoded owner/alpha/message/kappa, actual Parts/scratch/high and source-order event. NIT_PairDomain derives canonical arrays/lengths/S2/loop shapes; full mutable post and omitted-cell frame, all branch/error/abort cases retained.'
 if row=='TX1:156':
  if f.endswith('::qm31_sample'):return 'All SAME raw 32-byte blocks: RawCircleSampleActualPolicyUnconditionalV1.sampler_total_canonical supplies actual q and canonicality, internally used by NIX_SamplerLaw.packet and sampler_replies.'
  if f.endswith('::circle_fallback_point'):return 'NIX_FallbackLaw.deployed on exact First/Second index0/1, actual parameters[0,0,1,0]/[1,0,1,0]. Same mapper Err arm alone calls fallback. Global fallback row remains OPEN; this domain-specific CLOSED supporting packet supplies only reached calls.'
  return 'NIX_SecureOodLaw.wrapper_source with canonical q produced from SAME block; both mapper error constructors and both fallback rows retained; packet closes complete caller carrier.'
 if row=='TX1:215':return 'NIX_ResidualLog.packet internally reads all eight actual row cells, derives canonical intermediate replies and every field operand in chronological17-call Law/Domain. NIX_ResidualCut.packet substitutes them into K058/K059; all canonical input/frame and original parsed-Claims caller clauses retained. JFy_FieldTotal.sub/mul and FIv_PreparedTotal.add discharge arithmetic, no native multiplication.'
 return 'Observer literal None has no entered callee; NEF deployed cfg excludes Some backend. All inherited caller/runtime qualifications retained.'
for r in c['rows']:
 old=by[r['row']];calls=[]
 for f in old['canonical_callees']:
  closed=[x for x in byfun.get(f,[])if x['status']=='CLOSED'];cp=cm.get(f)
  support=r['row']=='TX1:156'and f.endswith('::circle_fallback_point')
  if r['admissible']:assert closed or cp or support,(r['row'],f)
  calls.append(dict(callee=f,basis_closed_rows=[x['row']for x in closed],basis_owners=[x['root_owners']for x in closed],co_candidate_row=cp['row']if cp else None,same_domain_support='NIX_FallbackLaw.deployed'if support else None,domain_derivation=domain(r['row'],f)if r['admissible']else 'No closure: pending full native dispatch positive root; child packets/domain helpers alone insufficient',original_callee_clauses=[cl for cl in old['obligation'].get('caller_domain_obligations',[])if cl.get('callee')==f]))
 out.append(dict(row=r['row'],admissible=r['admissible'],root_domain=r['root_domain'],calls=calls,original_external_clauses=[cl for cl in old['obligation'].get('caller_domain_obligations',[])if 'callee'not in cl],native_root=r['primary_root'],hypothesis_inventory='NJK_HYPOTHESIS_INVENTORY.json'))
(E/'NJK_CALL_DOMAIN_CHECK.json').write_text(json.dumps(dict(status='SIX_COMPLETE_PACKETS_ONE_EXPLICIT_OPEN_COMPOSITION',rows=out,global_support_rows_promoted=False,original_clauses_retained=True),indent=1)+'\n');print('NJK complete candidate call-domain inventory sealed')
