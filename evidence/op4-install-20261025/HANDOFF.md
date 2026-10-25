# Op4 scan row remains open: pinned translator failure

No checked row-closing theorem and no checked source/model counterexample were
obtained. No new Lean module was installed. This packet is failed-route evidence,
not the requested closure deliverable. S2 and the 100-bit target remain unestablished.

## Before and required after

Before: accepted_pair_claims quantifies arbitrary CurrentCaller Ops; op4 is
preserved by sdkOps, permitting RowShape_SlotObstruction's padding behaviour.
Required after (NOT PROVED): specialize only op4 to the whole extracted shipped
canonical_scan and retain every other slot and premise; derive successful Result
and OraclePortCompactDraft.scan (bytesOf f.proof.val) for the SAME returned f,s
and accepted native execution. That scan is called by OraclePortCompactDraft.parse
inside OraclePortStoredParserC4.parseReached. It covers y1, inactive+round0,
round1+final, all22 openings. No change to carrier, failure event or metric is proposed.

No hypothesis asserting scan or parsed provenance was introduced to obtain closure.
The existing FirstEntryVerifierConeJoin.parsed premise already entails frozen scan;
projecting it would not discharge this source row. MultiproofConeStrictScan.scan_total
is about the owned parser_reference.scan, not the shipped body. It was inspected,
not silently attributed to canonical_scan. Padding rejection for the actual installed
body was NOT checked; no claim to have passed the requested witness test.

## Exact blocker

Pinned Charon emits the complete scan parent and nested loops (001), and Aeneas
translates that parent while children remain external (001). Expanding concrete
children/decoders/constants succeeds in Charon002, but Aeneas002 exits2 with
`Uncaught exception: Not_found` in InterpReduceCollapse.collapse_ctx_following_sequence
(interp/InterpReduceCollapse.ml:1991). Existing `-loops-to-rec` mode on the same
child-expanded source (Aeneas003) also exits2 at that location. No tool was modified.

Split diagnostic: Charon003 excludes canonical_scan and selects echeck with concrete
decoders. Aeneas004 exits1: `Could not compute a loop fixed point in 2 iterations`
at crates/aspis-r1-cost-probe/src/verifier.rs:40:4–42:1; compiler
interp/InterpLoopsFixedPoint.ml:227. This identifies a narrower translator failure,
not proof that echeck disagrees with frozen2. Partial emission is excluded.
The exact commands, source snapshots, errors and caps are retained per attempt.

No unchanged timeout/memory-kill rerun occurred; none of these jobs timed out or
was killed. Recursive-loop mode changed extraction configuration; the next run
split the subtree. The pinned extraction route stops here rather than substituting
an unproved scan helper law, changing Rust/model bytes, or repairing the compiler.

## Validation

Only optimized release MIR extraction and Aeneas translation ran. Reused the
existing unchanged S2W_run_host.py; no launcher/monitor/build infrastructure was
written or repaired. All runs used their own verified systemd scopes with
MemoryHigh=6G MemoryMax=8G MemorySwapMax=0 TasksMax=64; no cap increase. At most
two task scopes overlapped (16 GiB total reservation, below the 55 GiB host limit).
No Lean build, Kani run, package replay, full manifest or ELF rebuild ran.
Lean budget 0/60 (including dependencies); Kani budget 0/20. #print axioms N/A:
no new theorem. Standard-axiom closure is NOT claimed. No template axioms imported.

| Attempt | Exit | Wall s | Peak RSS KiB | Swap |
|---|---:|---:|---:|---:|
|Op4I_aeneas001|0|12.552132|165968|0|
|Op4I_aeneas002|2|12.316976|158400|0|
|Op4I_aeneas003|2|15.078543|157152|0|
|Op4I_aeneas004|1|0.925455|109824|0|
|Op4I_charon001|0|55.219849|540848|0|
|Op4I_charon002|0|56.004493|539348|0|
|Op4I_charon003|0|64.779918|537372|0|

Every command records source revision 24b01cc808, exact SHA256s and original source
snapshots. pins.json also confirms inspected host candidate/verifier/compact/field/
wide_exact bytes match this checkout, and records tool hashes/sizes. attempt-summary.json
summarizes receipts; individual receipt.json/stdout.log/time.log are authoritative.

## Retained obligations and freeze

No assumptions were discharged, added or changed. All accepted_pair_claims premises
and D188 trust boundaries retain their original meanings. Source-body correspondence,
concrete child transport, full-scan law and same-accepted-execution composition
remain open. Next concrete proof deliverable: reuse an already pinned successful
child extraction (e.g. retained echeck) with checked nominal carrier/body transport,
then prove the emitted scan loop invariant and install only op4. This was not done.
No source mismatch is established; do not lower the row or replace its conclusion.

Only this evidence directory changed. No existing Lean module, shipped source,
cfg(kani) harness, session A worktree/candidate, key, feature, parameter or wire format
was touched. ELF rebuild trigger did not fire. Inherited pins (not reproduced):
default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4,
devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299,
Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548.
All task jobs terminal; another owner's scope was observed and left untouched.
No binaries, objects or archives committed; raw generated templates are text-only
excluded evidence. Commits local; no push.
