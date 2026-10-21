# Continuation adoption scope

No shipped file changes. The generator pins frozen candidate.rs and multiproof.rs;
--check validates all cut bodies and output bytes. The binary_level cut is one
complete outer iteration of verify_in_place with Arity::Two. The leaf iteration
is the complete key-read/cursor/hash/duplicate/write body of batch_tree.

The first direct whole-level BMC timed out while unrolling, with no completed
solver result. It is not evidence. Its 512-byte diagnostic bound also does not
cover every frozen slot. The replacement attempts a full-state source_row contract followed by a
composed level gate, both using the entire
5504-byte maximum slot bound (172*32). The leaf-hash wrapper has no external
mutable state: its exact digest, event byte, call count and input lengths are
part of the verified return contract. Source_row is intended to return every scratch byte, cursor and oracle effect.
Its currently UNVERIFIED contract does not weaken these
postconditions to a single coordinate.

Each final step harness uses universally arbitrary scratch and oracle-event
observation coordinates. The level answer tape has independent answers by
call ordinal. Equality of all ordinals/bytes plus exact call count/component
lengths identifies the ordered local oracle transcript. Rejection retains
partial scratch and skips the remaining work. These are P6 certificates,
not kernel conversion of Kani output into Lean theorems.

The generated adoption_level.rs factors the exact binary_group into source_row,
retaining the source i<n loop, updates and n=w. Its control/template extraction
is a trust boundary alongside the frozen-cut ledger. The induction in
MultiproofConeLevelIteration proves exact full-Result equality between structural
iteration and the actual extracted MultiproofConeRef.reference.levels through
height 18. adopt_eighteen explicitly requires the one-level source equation;
it is not a claimed proof of that P6 boundary inside Lean.

The selected opening is supplied to the leaf step together with its key and
relative-position projection. Mapping that borrowed slice to the stored proof
and linking batch_keys/sort/count/padding/final root to the reached caller remain
separate. Caller lowering waits on S2. No AcceptedRunJoin is constructed here.

Final disposition: the direct whole-level attempt and both full-state row
contract attempts timed out with zero completed solver results. Inlining the
byte reader did not remove the propositional-reduction bottleneck. The composed
level gate was NOT RUN because its verified-callee prerequisite is missing.
Do not use source_row as a verified stub in a claimed certificate. The leaf
contract and leaf-batch step both passed; the height induction is conditional
on the precise one-level certificate and preservation premises. This packet
stops at the requested resource blocker, without a cap increase or a complete
source-cone claim. A next attempt should isolate the sibling/short/occupied
full-state frames and symbolic slice window before composing a level.
