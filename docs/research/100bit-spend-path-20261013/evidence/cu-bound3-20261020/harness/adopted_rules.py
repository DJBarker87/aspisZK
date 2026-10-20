"""Add code-cited new-format rules to byte-rebased second-method rules.
Usage: adopted_rules.py rebased.json out.json
No observed maxima substituted for input-dependent new-format loops.
"""
import json,sys
r=json.load(open(sys.argv[1]));V=['stage1','stage2']
def cap(id,addrs,N,citation,roles=V):
 for role in roles:r['loop_caps'].append(dict(id=id,role=role,addr=addrs,N=N,citation=citation))
def ex(id,addr,reason,citation,arm='t'):
 r['exclusions'].append(dict(id=id,role='*',addr=[addr],arm=arm,reason=reason,citation=citation))
ex('X-BINARY-ARITY','0xa66a0','The only deployed node_count caller passes Arity::Two; the Eight arm cannot execute on the adopted route.', 'crates/aspis-r1-cost-probe/src/candidate.rs:135; multiproof.rs:44,71')
cap('C-BINARY-LEVELS',['0xa6850','0x13390'],18,'multiproof.rs:29,45-46,71,147: LEAF_BITS=18, Two.bits()=1; exactly 18 levels.')
for role,n in [('stage1',11),('stage2',13)]:
 cap('C-BINARY-PARENTS',['0xa6870','0x133e8'],n,'candidate.rs:98-102,135,141: batch size 10 (A) / 12 (B); at every level distinct parents <= batch size, plus one exit test. multiproof.rs:71-85,147-189. Globally parent iterations = supplied_nodes + distinct_leaves - 1; six-slot supplied_nodes <=914 by evidence/proof-size-20261019/REPORT.md section 1 counting bound (420 A, 494 B; parent totals <=447 A /527 B).',[role])
 cap('C-BINARY-CHECK-INDICES',['0xa6388','0xa63e8','0xa6490','0xa6510'],n,'multiproof.rs:54-58: windows/indices scans <= batch size 10/12 plus exit; candidate.rs:98-102 dedup only reduces count.',[role])
 cap('C-BATCH-INSERT',['0x12ae8'],n,'candidate.rs:111-118: insertion-sort j strictly decreases from i < n; inner trips <=n, plus exit; dedup loop visits n=10/12 keys.',[role])
ex('X-BATCH-NONEMPTY','0x12eb8','This is the empty-key-iterator check in the d==0 first-key path. n is 10/12, so the first key exists; after consuming it d>=1 and this path is not revisited.', 'candidate.rs:98-102,119-132; ELF 0x12ba0 d==0 branches to 0x12e90, 0x12eb8 compares keys.begin to keys.end before its first read.')
cap('C-FOLDED-DUPLICATE-RUN',['0x12be8'],5,'candidate.rs:103,120-132: transcript queries are distinct (r0_transcript.rs:205-211), each folded index u/4 has at most four preimages. This key-iterator inner loop visits at most three duplicate keys after one unique key plus the next distinct key or exit, <=5 header executions; C1/C2 have no duplicates.')
cap('C-NODECOUNT-CHILDREN' ,['0xa68d8'],3,'multiproof.rs:76-79: sorted distinct binary children of one parent are at most 2, plus exit test; counts summed over levels <= supplied_nodes+2*distinct-2. Evidence/proof-size-20261019/REPORT.md section 1: at most 914 supplied nodes across all six slots.')
cap('C-SLOT-PADDING',['0x132c0'],689,'candidate.rs:135-139: count <= SLOT_NODES[s], padding scan chunks_exact(8) visits <=4*SLOT_NODES[s] <=688, plus exit test; compact.rs:56 SLOT_NODES=[146,146,128,172,172,150]. Six slots <=914 nodes (proof-size-20261019/REPORT.md section 1).')
cap('C-COMPACT-ROWS',['0xa6b90'],28,'compact.rs:30,172-189: exactly 27 framed rows, sizes from r1_wire::row_shape, plus exit. Rows 14..26 expand 426 values; y1 expands 29 values (compact.rs:34-38). Every canonical/expansion scan has fixed input length.')
cap('C-BATCH-TREES',['0x126e0'],3,'candidate.rs:106: for tree in 0..3; exactly three commitment trees per batch.')
for role,n in [('stage1',11),('stage2',13)]:
 cap('C-INSERT-OUTER',['0x12ad8'],n,'candidate.rs:111: for i in 1..n, n=10/12 by batch selection; plus exit test.',[role])
 cap('C-BATCH-LEAVES',['0x12b78'],n,'candidate.rs:120: iterate keys[..n] once; n=10/12, plus exit test.',[role])
cap('C-CANONICAL-OPENINGS',['0x8f9e8'],23,'candidate.rs:63: for i in 0..22, plus exit test; opening has fixed 832-byte layout.')
cap('C-CANONICAL-SLOTS',['0x8fa98'],5,'candidate.rs:65-72: four subslots per opening; 26 M31, one K, two K per subslot, plus four wide folded fields; fixed canonical scan trip counts.')
cap('C-COMPACT-COPY',['0xa6d80'],'observed','compact.rs:172-189 and r1_wire.rs:row_shape: every row payload size and every copy length is a compile-time constant; 27 rows always processed; accepted framing cannot change copy lengths. The per-entry maximum is attained in every stage-1 scan.')
cap('C-CANDIDATE-TX1',['0x14288'],11,'candidate.rs:193,208-209: k must equal SPLIT=10; a.next starts at zero and query_values increments it once; ten queries plus exit test.', ['stage1'])
cap('C-CANDIDATE-TX2',['0x12298'],13,'candidate.rs:223-231: resume requires a.next==SPLIT=10; exactly 12 remaining queries of 22, plus exit test.', ['stage2'])
# Old stage1 body changed, so its address rule was deliberately not rebased.
# The actual checkpoint scan address is added only after disassembly/source mapping.
json.dump(r,open(sys.argv[2],'w'),indent=1)
