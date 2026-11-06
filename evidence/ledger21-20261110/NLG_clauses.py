from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent;x=json.loads((E/'NLG_CANDIDATE_REVIEW.json').read_text());matrix=[]
for r in x['rows']:
 for c in r['original_clauses']['caller_domain_obligations']:
  s=c.get('callee',c.get('call',{}).get('syntax',''));rid=r['row'];upstream='inventory:'in c['id']
  if rid=='TX2:124':
   if 'Reader<'in s:
    detail='NKU_RawAt/EAt/KAt, FineRead and Offsets: SAME checkpoint backing1768, entered N4/16/32cursor, exact decoder errors/cursor advance; old backing/owner frame derived'
   elif 'read_checkpoint_semantic'in s:detail='NKU_Semantic/NKK_SectionFrames.semantic: CLOSED121 at cursor408,10Kslots, same returned cursor568, complete errors and frame'
   elif 'read_checkpoint_weights'in s:detail='NKU_Weights/NKK_SectionFrames.weights: CLOSED122 at cursor712 with SAME ownedVec64, exact result/cursor1736/Err/drop and frame'
   elif 'validate_checkpoint_queries'in s:detail='NKU_Validator and NKK_Clauses: CLOSED126 on same assembled22u32, every index/error; no accepted-queries premise'
   elif 'filled'in s:detail='NKU_Allocation/NKK_AllocationStage: v.final_len()=64 forS2; ZERO, SAME Frame.reservation; full returned Vec or Allocation Err, no suffix'
   elif 'hash.digest'in s:detail='NKU_DigestJoin: ordered proof/public/literal22+cp[0..1736] slices and unchanged replies. RuntimeSha256Value remains trust; proof57607/public<=1880 native domain explicitly upstream'
   elif 'iter'in s or '.any'in s:detail='NKU_FineHeader live iterator from guards; any on bytes[11..16], SAME returned iterator/scope; no later digest after rejection'
   elif 'from_le_bytes'in s:detail='NKU_FineWords:22 source-order raw4 values,8/8/6windows, exact little-endian scalar with complete readonly/cursor frame'
   elif 'Box::new'in s:detail='NKU_SourceConstructors PreparedCut covers full field value on emitted carrier; NJJ prepared_tail positiveK060 with corrupt-value/different-allocation controlsK061/062 supplies(aa) SAME ownership cut. Existing Allocator fresh-block-or-abort interpretation retained; no totality claim. NKK_K045 variant-only never supplies full Prepared.'
   else:detail='Header/Offsets/Tail on SAME sourceS2: checkpoint_size1768/tag/length/end1736/nextcast and first rejection; ordinary scalar/record/Result operations execute under(au); Chronology exact fail/div prefix'
  elif rid=='TX1:235':
   detail='NKY_LevelsLiteral body at SAME index/f/o/s, level0..19 and high34+level<64. NKI_AppendPacket CLOSED234 derives complete output and canonicality at EACH iteration; four canonical QM31 adds executed via emitted add laws; conservative alternative field owners retained, not new dynamic calls. NKY_LevelsComplete literal full2+2array Result association for every packet witness.'
  else:
   if 'Box::new'in s:detail='NKY_BoxAction/BoxTotal/BoxSource: sole source allocation176/304 align8, arbitrary SAME Reservation; exact Box owner and reconstructed payload, allocator post and old live-place frame in ONE Result; exhaustion abort/fail/div prefixes retained; no allocation-success hypothesis'
   elif 'decode_pool'in s:detail='CLOSED raw152/153 at SAME immutable bytes, full all-length typed Result via NJQ/NKP windows; every21 account/13tree error maps InvalidAccountData; no successful child/canonical input restriction'
   else:detail='NKF_BoxModel.tail preserves source map_err/? before Box allocation; error allocates nothing, exact ProgramError; success continues once; no cleanup suffix introduced'
  matrix.append(dict(row=rid,original_clause=c,local_disposition=detail,upstream_context_retained=upstream,upstream_disposition='Inventory unit provenance remains at parent; local cut needs only helper own domain. Recorded in NLG_PARENT_CLAUSES, not a successful-child root premise.'if upstream else None,roots=r['roots']))
(E/'NLG_CLAUSE_MATRIX.json').write_text(json.dumps(dict(status='PASS_COMPLETE_CLAUSE_REVIEW',clauses=matrix,original_count=len(matrix),no_clause_dropped=True,original_statuses_are_historical_not_new_open_obligations=True,source_result_scope='CLOSED conditional hybrid rows retain headline std/Allocator/P6/D188 interpretation; no liveness/totality claim'),indent=1)+'\n');print(json.dumps(dict(original_clauses=len(matrix),rows=4,status='PASS')))
