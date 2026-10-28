# NBI batch bridge

**OPEN. No headline premise removed; TX2 U09 remains OPEN.** Full joint
statement is inherited from NBE_batch_BRIDGE.md: both transaction splits,
all three actual root calls in order, SAME scratch, all Results and issued
hash prefixes, exact first-error short circuit. Frozen source unchanged.

## Local progress

K020 checks the actual post-hash duplicate/equal/reject/new-key decision;
K021/K022 check one new-index and one leaf write, with arbitrary surrounding
state; K023 the distinct-count advance. The leaf hash remains before dedup,
including on a duplicate that rejects. NBI_BatchDomains derives the write,
predecessor, increment and padding iteration bounds from both actual splits.
No global query-uniqueness assumption is added.

K024 checks ONE arbitrary8-byte little-endian padding predicate. K025 checks
ONE chunk iterator read on arbitrary surrounding bytes. K026 derives the
counted suffix's whole-word bounds; K027 the actual split/slot arithmetic;
K028 padding short-circuit call count; K029 counted verifier-prefix region.
NBI_Padding.any_eq_scan supplies total induction over the ACTUAL installed
iterator (including predicate fail/div, true/false, exact iterator remainder).
first_stop retains the exact unvisited suffix on the first nonzero word;
no whole-buffer solver run or accepted-only final scan equation is assumed.

## Exact open members

1. NBI_NativeBatchLeafTraversal: combine key/physical-opening/leaf producer,
   same-scratch post-hash dedup steps and inherited loop induction for ALL
   return paths, including the hash issued before duplicate rejection. A
   passing post-hash branch is not an independent successful leaf execution.
2. NBI_NativePaddingPort: bind the actual chunks_exact suffix and native
   u64 predicate to the installed iterator/predicate on the same proof bytes,
   including initial count>SLOT_NODES and precise Parse/Merkle result choice.
   Local chunk/word gates and total installed induction are predecessors.
3. NativeCountScanPort/NativeNodeGatePort/NativeVerifyControlPort from the
   multiproof report remain OPEN; batch cannot claim CLOSED callee bridges.
4. NBI_NativeBatchTreeJoin: compose SAME sorted/key/leaf/count/padding/verifier
   execution and retained scratch/log. Then bind the exact three calls and
   batch_merkle's Prepared/root projections. No independent per-tree success
   or equal-output-only assertion can replace that call-order proof.

Inherited NBE_ParserOpeningDomain stays an explicit producer obligation.
No XRn_Join kit/stand-in or new trust item is introduced. Runtime/heap/ABI,
crypto oracle-value and frozen source-to-ELF obligations remain unchanged.
