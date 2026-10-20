"""Code-cited caps at newly derived frozen-ELF sites. No verifier edits.
The three batch-tree calls are unrolled in this ELF; each copy is accounted.
"""
import json,sys
from pathlib import Path
H,A,inp,out=map(Path,sys.argv[1:]);r=json.loads(inp.read_text())
def cap(id,role,aa,n,cite):
 r['loop_caps'].append(dict(id=id,role=role,addr=aa,N=n,citation=cite,citation_revision='b2727acd3 frozen; fa894d83d task base'))
for role,n in [('stage1',10),('stage2',12)]:
 cap('F-INSERT-OUTER',role,['0x298a0','0x2a9d0','0x2bcf8'],n+1,'candidate.rs:109-118 sort_batch_keys: outer 1..n; batch_tree :173-176 sets n=10/12; three explicit calls :165-167, no outer tree loop remains.')
 cap('F-INSERT-INNER',role,['0x298b0','0x2a9e0','0x2bd08'],n+1,'candidate.rs:112-116: j starts i<n and strictly decreases on every swap, at most n iterations plus exit.')
 cap('F-BATCH-LEAVES',role,['0x29948','0x2ab38','0x2bda8'],n+1,'candidate.rs:178-195: key_position starts 0, advances once before any continue, stops at n=10/12. Every query is visited exactly once per tree.')
 cap('F-FOLDED-DUPLICATES',role,['0x299f8','0x2abe8','0x2be60'],5,'candidate.rs:102,178-195: sorted equal folded indices are u/4; distinct transcript queries (r0_transcript.rs:205-211) give at most four preimages, plus the next-key/exit check. C1/C2 indices are distinct. Compiler inner continue cycle cannot exceed this run length.')
 cap('F-SLOT-PADDING',role,['0x2a078','0x2b280','0x2c6c8'],689,'candidate.rs:196-200: padding chunks_exact(8), count<=SLOT_NODES[s]; compact.rs:56 capacities [146,146,128,172,172,150], at most 4*172 words plus exit.')
 cap('F-BINARY-LEVELS',role,['0x2a148','0x2b330','0x2c7e8'],18,'multiproof.rs:147-189 verify_in_place: LEAF_BITS=18, Arity::Two.bits()=1, exactly 18 levels; candidate.rs:202 fixes binary arity.')
 cap('F-BINARY-PARENTS',role,['0x2a1a0','0x2b378','0x2c848'],n+1,'multiproof.rs:147-189: distinct parents at any level <= distinct initial leaves <= batch size 10/12, plus exit. candidate.rs:173-176 fixes batch sizes, :202 fixes binary arity. Parent totals <=447/527 by 420/494 supplied nodes +30/36 leaves -3 roots (proof-size-20261019/REPORT.md section 1).')
 cap('F-QUERY-LOOP',role,['0x2da60' if role=='stage1' else '0x12d50'],n+1,'candidate.rs:239-251 query_loop: each successful query_values advances a.next once via verifier.rs:287-290; tx1 :280-286 starts 0 and ends SPLIT=10; tx2_common :295-310 resumes exactly 10 and ends 22. Error states exit. Loan-scope moves/destructuring at :311-315 do not introduce further iteration.')
 cap('F-GEOMETRY-QUERIES',role,['0xb4e70'],n+1,'verifier.rs:148-177 QueryGeometry::for_range iterates queries[start..end], lengths 10/12 by candidate.rs:284,307; five denominators per query and no accepted early zero return.')
 cap('F-GEOMETRY-PREFIX-BACKWARD',role,['0xb5908','0xb5b40'],5*n+1,'verifier.rs:134-144,167-174: batch_prefix_products visits flat.len()=5*(end-start), backward inversion visits precisely the same flat length; accepted ranges have 10/12 queries.')
 cap('F-BATCHED-WEIGHTS-NEW',role,['0xb5ff0','0xb6088'],65,'verifier.rs:205-215: raw initialization and index loop visit weights.len()=64 (transport.rs final_len(S2), Accumulator::new and resume); compiler peeled first fill leaves 63. At most 64 plus exit.')
 cap('F-BATCHED-WEIGHTS-FINISH',role,['0xb6190'],65,'verifier.rs:226: finish iterates all 64 weights once. candidate.rs:286,311-315 ends query_loop before finishing moved weights; the move is constant-size and neither duplicates nor retries a query.')
 cap('F-ACCUMULATE-BASIS-OUTER',role,['0xb6410'],7,'verifier.rs:278-280: n doubles from 1 until width=64; six iterations plus exit; transport.rs final_len(S2)=64.')
 cap('F-ACCUMULATE-BASIS-INNER',role,['0xb6480'],33,'verifier.rs:280: inner 0..n, n in {1,2,4,8,16,32}; at most 32 plus exit.')
 cap('F-ACCUMULATE-WEIGHTS',role,['0xb6690','0xb6818'],65,'verifier.rs:281-290: 0..width=64; update_residue_row :235-244 always has four limbs, flush depends only on terms modulo four. terms advances once per query. The alternate compiler loop is the same 64-weight scan, not an input-sized loan retry.')
# Same source fact as cu-bound3 X-BATCH-NONEMPTY, re-derived for all three copies.
r['exclusions'].append(dict(id='F-FIRST-KEY-NONEMPTY',role='*',addr=['0x29c80','0x2ae68','0x2c0e8'],arm='t',
 reason='Each check is reached only through d==0. d starts zero, the first unique leaf increments it, and it never decreases. Thus key_position is still zero at this first-key check. n is 10/12, so key_position>=n is impossible; the compiler branch to downstream multiproof loops cannot execute here.',
 citation='candidate.rs:173-195; ELF: r6=0 at 0x29938/0x2ab28/0x2bd90; d==0 dispatch at 0x29978/0x2ab68/0x2bdd8 targets first-key check 0x29c78/0x2ae60/0x2c0e0. Checks compare r6 to n loaded from [r10-0x578]; n in {10,12}. This re-derives predecessor X-BATCH-NONEMPTY, rather than carrying an unmatched address.',citation_revision='b2727acd3 frozen'))
# Finish-relation loop address is set after mapping its frozen body, below.
for role in ['stage1','stage2']:
 d=json.loads((A/f'{role}.json').read_text());lm=json.loads((A/f'lines-{role}.json').read_text())
 for l in d['loops']:
  if 'finish_query_dot' in l['function']:
   fr=(lm.get(l['header']) or {}).get('frames',[])
   # Only the concrete final dot scan is admitted here; no function-wide guess.
   if l['header']=='0xbc530':
    cap('F-FINISH-QUERY-DOT',role,[l['header']],65,'verifier.rs:301-305 finish_query_dot: j advances once until weights.len()=64; finish_relation :312-321 checks relation then this 64-term dot, then a.next==22. candidate.rs:311-321 creates the relation view once after ending the 12-query loop. Polynomial evaluation is exactly seven coefficients (:292); rounds are fixed by Variant::S2.')
json.dump(r,out.open('w'),indent=1);print('frozen code-cited rules',len(r['loop_caps']))
