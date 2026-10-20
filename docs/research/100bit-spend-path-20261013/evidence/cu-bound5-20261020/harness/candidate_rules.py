"""Candidate source caps after strict bound4 instruction-body rebasing.
No source edits. Source-sensitive exclusions are reattached to current lines.
New canonical-scan loops require current ELF/debug-map inspection.
"""
import json,sys
from pathlib import Path
H,A,inp,out=map(Path,sys.argv[1:]);r=json.loads(inp.read_text())
revision='c16e59e77 candidate; task base 2318acd430'
citations={
'C-BINARY-PARENTS':'multiproof.rs:85-109 node_count: each distinct parent is written once, never increasing n; candidate.rs:174-196 bounds initial leaves by 10/12, plus loop exit. Parent totals <=447/527 from compact.rs:54 capacities and three roots.',
'C-BINARY-CHECK-INDICES':'multiproof.rs:54-58: windows and domain scans visit at most d leaves; candidate.rs:174-196 gives d<=10/12. At most batch size plus exit.',
'C-NODECOUNT-CHILDREN':'multiproof.rs:96-105: sorted distinct binary children of one parent are at most two, plus exit. Candidate passes binary arity at candidate.rs:196.',
'X-ROUTE-ADAPTER':'programs/r1-cost-probe/src/r1_pool_adapter.rs:1032-1043 dispatches lifecycle tags 4/5/6 separately. Admitted stage 1 is [3,10]; [3,11] reaches stage1 but candidate.rs:270-274 rejects k != SPLIT=10. Settlement is the stage2 route.',
'C-WEIGHTS-PAIR':'weights.rs:238-286: n=64 for S2 two folds (transport.rs:8); kinds [1,2,3,5,6], three tensor factors of four, 4 x 16 shared-point terms, and 2 x 4 high terms. The constant-shape maximum is attained in every accepted relation call.',
'C-CANONICAL-OPENINGS':'candidate.rs:59-71: exactly 22 openings of fixed 832-byte layout; compact.rs:28,37,47. At most 22 trips plus exit.',
'C-CANONICAL-SLOTS':'candidate.rs:61-68: exactly four subslots per opening, 26 M31 values, one K and two more K values per subslot. At most four trips plus exit.',
'C-COMPACT-ROWS':'compact.rs:29,150-173: exactly 27 framed rows, lengths from r1_wire::row_shape, plus exit. Each accepted copy/check length is fixed by row_shape.',
'C-COMPACT-COPY':'compact.rs:150-173 and r1_wire.rs:39-48 row_shape: each of 27 accepted row payload sizes and copy lengths is fixed by the row index; accepted framing cannot lengthen copies.',
'F-INSERT-OUTER':'candidate.rs:104-111 sort_batch_keys: i in 1..n; batch_tree :174-177 fixes n=10/12. Three explicit calls :166-168; each outer loop has at most n trips plus exit.',
'F-INSERT-INNER':'candidate.rs:106-109: j starts i<n, strictly decreases on swaps and cannot underflow. At most n trips plus exit.',
'F-BATCH-LEAVES':'candidate.rs:178-195: key_position starts 0, increments once before any continue and stops at n=10/12; each query is visited once per tree.',
'F-FOLDED-DUPLICATES':'candidate.rs:94-97,178-195 and r0_transcript.rs:205-211: transcript queries distinct; only folded u/4 indices can coincide, at most four preimages plus next-key/exit. C1/C2 indices distinct.',
'F-SLOT-PADDING':'candidate.rs:196-200: padding scanned in 8-byte chunks, count<=SLOT_NODES[s]; compact.rs:54 capacities [146,146,128,172,172,150]. At most 4*172 words plus exit.',
'F-BINARY-LEVELS':'multiproof.rs:147-189 verify_in_place: LEAF_BITS=18, Two.bits()=1, exactly 18 levels; candidate.rs:202 fixes binary arity.',
'F-BINARY-PARENTS':'multiproof.rs:147-189: at each level distinct parents <= distinct initial leaves <=10/12; plus exit. candidate.rs:174-175,202. Parent totals <=447/527 from supplied nodes 420/494 + leaves 30/36 - 3 roots; compact.rs:54 and proof-size-20261019/REPORT.md section 1.',
'F-QUERY-LOOP':'candidate.rs:239-251,280-286,295-315: query loop starts at 0 (tx1) or checkpoint 10 (tx2) and ends at 10/22; verifier.rs:289-301 increments a.next exactly once per success. Borrow moves do not restart it.',
'F-GEOMETRY-QUERIES':'verifier.rs:156-184: for queries[start..end], length 10/12 via candidate.rs:284,305-307; exactly five denominators per successful query.',
'F-GEOMETRY-PREFIX-BACKWARD':'verifier.rs:142-152,175-181: prefix and backward loops each visit flat.len()=5*(end-start), with accepted range length 10/12.',
'F-BATCHED-WEIGHTS-NEW':'verifier.rs:214-222: raw fill and conversion visit weights.len()=64, fixed by transport.rs:8 and Accumulator::new/resume. At most 64 trips plus exit.',
'F-BATCHED-WEIGHTS-FINISH':'verifier.rs:234: one pass through 64 weights. candidate.rs:286,311-315 finishes only after query_loop; moved weights are not retried or duplicated.',
'F-ACCUMULATE-BASIS-OUTER':'verifier.rs:289-292: width=64; n doubles from 1, six iterations plus exit; transport.rs:9 final_len(S2).',
'F-ACCUMULATE-BASIS-INNER':'verifier.rs:292: j in 0..n, n in {1,2,4,8,16,32}; at most 32 trips plus exit.',
'F-ACCUMULATE-WEIGHTS':'verifier.rs:293-301: width=64 scan once per query; update_residue_row :243-251 has four limbs, flush determined by terms modulo four. No input-sized borrow retry.',
'F-FINISH-QUERY-DOT':'verifier.rs:313-332: j increases once until 64 weights; relation rounds fixed by S2 and polynomial :304 has seven coefficients; candidate.rs:311-321 constructs relation view once.',
'X-VEC-CHECKPOINT':'verifier.rs:32,340-376: capacity checkpoint_size(S2) equals the sum of the fixed header, roots, scalars, queries, two points, 64 weights and trailing digest; helpers each serialize once; final length assertion rejects any mismatch.',
'X-VEC-GEOMETRY':'verifier.rs:156-184: line_z capacity=end-start, flat capacity=5*(end-start), prefixes/flat_inverse capacity=flat.len(); pushes/resize exactly fill them. collect consumes an exact-size range.',
'X-VEC-HEAP':'aspis-core/src/r0/heap.rs:5-10: try_reserve_exact(n) before resize(n). verifier.rs:214-222 and weights.rs:239-243 fix n to 64 for S2.',
'X-S2-GROUPED':'weights.rs:76-77,238-243,312-313: S2 two-fold final message has exactly 64*32 bytes; grouped_inactive_pair therefore takes its S2 fast path. transport.rs:8-9 fixes S2 folds/final_len.',
'X-WEIGHTS-S2':'weights.rs:238-265,289-315 and transport.rs:8: S2, folds=2 fix D/one-fold/non-S2 Libra arms. shared_two_point follows statement point rows differing only at coordinates 6/7, while factors d2/d3 read 5,4,9,8 (TAU=[3,4,2,0,1]); state_only_prefix.rs:600-614 and weights.rs:162-178.',
'X-PROOF-S2':'candidate.rs:40-48,76-86 fixes Variant::S2; verifier.rs:321-326 uses that variant for relation; weights.rs:314 selects the S2 Libra path; transport.rs:8.',
'X-BINARY-ARITY':'candidate.rs:196,202 explicitly passes Arity::Two to node_count and verify_in_place; multiproof.rs:44,71 distinguishes the unexecuted Eight arm.',
}
for cat in ['loop_caps','exclusions','callee_caps']:
 for e in r[cat]:
  if e['id'] in citations:
   e['predecessor_citation']=e['citation'];e['citation']=citations[e['id']];e['citation_revision']=revision
  if e['id']=='X-S2-GROUPED':e['ws_regex']=r'weights\.rs:(76|77)$'
  if e['id']=='X-WEIGHTS-S2':e['ws_regex']=r'weights\.rs:(24[4-9]|25[0-9]|26[0-5]|288|289|30[6-9]|31[0-5])$'
  if e['id']=='X-PROOF-S2':e['ws_regex']=r'transport\.rs:8$|weights\.rs:314$'
# The first-key check's entire function is instruction-matched, not guessed.
# Keep exact old/new ELF correspondence, with the current source invariant.
for e in r['exclusions']:
 if e['id']=='F-FIRST-KEY-NONEMPTY':
  e['predecessor_citation']=e['citation']
  e['citation']='candidate.rs:178-195: d and key_position start zero. The d==0 first-key check occurs before the first unique leaf increments d; d never decreases. Thus key_position is zero there and n=10/12 is nonzero (:174-175). All three copies are mapped by equal whole-function instructions in rule-address-mapping.json.'
  e['citation_revision']=revision
# The candidate line tables identify canonical_scan but return line '?'
# for both headers. Re-derive their bounds from current instructions, not
# an old address delta. canonical-scan-disassembly.txt records full context.
import struct
import sbf_slack as S
elf=(H/'artifacts/verifier/linked.elf').read_bytes();tx=next(x for x in S.elf_sections(elf) if x['name']=='.text')
def insn(addr):return struct.unpack_from('<BBhi',elf,tx['offset']+addr-tx['addr'])
assert insn(0xc3d78)==(0xb7,1,0,0)  # outer counter begins zero
assert insn(0xc3db0)==(0xa5,1,1,22) # outer limit 22
assert insn(0xc3e30)==(0xb7,1,0,1) # inner counter begins one
assert insn(0xc40c8)==(0x07,1,0,1) # inner counter increments
assert insn(0xc40d0)==(0xa5,2,-82,4) # exactly four subslot bodies
for role in ['stage1','stage2']:
 d=json.loads((A/f'{role}.json').read_text())
 for header,id,n in [('0xc3da0','C-CANONICAL-OPENINGS',23),('0xc3e48','C-CANONICAL-SLOTS',5)]:
  l=next(x for x in d['loops'] if x['header']==header)
  assert 'canonical_scan' in l['function'] and max(l['max_trip_per_entry'])<=n
  r['loop_caps'].append(dict(id=id,role=role,addr=[header],N=n,citation=citations[id]+' ELF: canonical-scan-disassembly.txt; counter initializations 0xc3d78/0xc3e30, bounds 0xc3db0/0xc40d0 and increment 0xc40c8.',citation_revision=revision))
r['target_revision']=revision
out.write_text(json.dumps(r,indent=1)+'\n');print('candidate rules',len(r['loop_caps']),'loop caps')
