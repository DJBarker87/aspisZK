# Op4 P6 scan closure

Branch `codex/cx-op4-p6-20261025`. TX1 scan/op4 is closed at the existing P6
source/reference trust boundary. **S2 and the 100-bit target remain open.**
No deployed soundness or fresh source-to-ELF release claim is made.

## Checked conclusion

`lean/Op4P_Accepted.lean`,
`AspisR1.Op4P_Accepted.accepted_pair_claims_op34`, builds directly on
`Op3I_Accepted.accepted_pair_claims_op3`. It specializes exactly op4 to the
whole extracted owned reference. Op3I's concrete op3 and every other operation,
binder, premise and conclusion are retained. The theorem destructures Op3I's
accepted pair once and exports the successful op4 call and frozen2
`OraclePortCompactDraft.scan (bytesOf f.proof.val)` for THAT SAME `f,s,cuts`
and accepted native execution. It does not select a second proof or cut.

The scan includes y1, inactive, round0, round1, final and all22 openings.
No scan law, canonicality, parsed provenance or whole-parser success is added
as a premise. `before-statement.lean.txt`, `after-statement.lean.txt` and
`premise-audit.json` audit the full statements mechanically: after removing
the added scan conclusion, the after statement is byte-identical to the
consistently op4-specialized before statement. This restricts the old arbitrary
operation family to one source instance; it is not equivalence with every
old dictionary. No cryptographic hypothesis or failure event changes.

`Op4P_Refinement.reference_total` proves the whole extracted reference equals
the frozen2 nonsemantic scan at the deployed length, with both inner Result
outcomes. `Op4P_Cuts.same_cut_scan` obtains that length from Op3I's actual
successful header on the same cut and scan success from TX1 reachability.
`Op4P_Install.other_slots` checks exact restoration of the other slots.

## Source equivalence and non-vacuity

The owned Rust reference is `kit/src/Op4P_reference.rs`, newly extracted by
Charon/Aeneas001 without the shipped-child translation failures. Its pure
recursive bodies are byte-identical to the prior MultiproofParserRef source;
`scanner_emission` proves structural equality of their emitted fixpoints,
without evaluating a concrete recurrence. The only generated normalization
is the naming-only discriminant instance expansion already used by Op3I.

`P6-EQUIVALENCE.md` records the source-step certificate and loop composition.
Kani002 proves full Result equality for an arbitrary opening's complete
shipped loop body;003 covers all464 y1 bytes;004 covers the generic actual
wide32 step;007 binds each of22 openings to its original stored slice;008
checks every wide-chunk ordinal in all three actual source ranges. All use
actual field decoders, exact pinned source bodies, arbitrary bytes and only
loop-bound assumptions. No Kani stubs or assumed source law. Both scans have
empty mutable/oracle/allocator/observer effects on success AND rejection.
The normal effect-free loop induction is recorded under existing P6 execution
semantics; no single whole-array Kani theorem or kernel proof of the shipped
Rust is claimed. This external P6 association and D188 native extraction
association remain explicit trust boundaries, not new Lean axioms.

`Op4P_Audit.witness_success` checks an existing symbolic header fixture also
succeeds in the new scan. `extraction_satisfiable` constructs the existing
specialized D188 association for arbitrary remaining dictionaries. These
establish local non-vacuity; they do not newly certify joint native/runtime/
crypto acceptance. `rejects_padding` excludes RowShape_SlotObstruction.badScan;
`rejects_padded` also excludes its57,607-byte extension with the identical
noncanonical first scanned word, so length rejection is not the only test.

## Validation and frozen target

Budget used: **15/80 Lean,8/40 Kani**; no package/full-manifest replay or ELF
build. Every job used its own scope:6G high,8G max,swap0,tasks64; Lean-j1-M7000
and optimized Rust. Lean ran sequentially after the14:00 UK window. At most
three task scopes overlapped (24GiB reservation, below the55GiB host limit).
Unchanged S2W launchers and the coherent SInt2 objects were reused. No build,
launcher or monitoring infrastructure was modified. Existing candidates and
other worktrees were untouched.

Final top target: Op4P_lean013, exit0,2.031096961s,5,142,052KiB peakRSS,swap0.
Final audit: Op4P_lean015, exit0,3.055305580s,5,253,588KiB peakRSS,swap0.
Their source revision anchor is beeeb53ccf plus the exact dirty source hashes
in the receipts; final checked bytes are committed in this branch. Each new
theorem has a successful #print axioms audit, limited to
[propext,Classical.choice,Quot.sound] (some use fewer). `validation-summary.json`
indexes every exact command,target,source hash,dependency fingerprint,exit,
wall,RSS,swap and axiom result. Failed elaboration audits are excluded.
`host-object-and-tool-pins.json` records final objects/tools as hashes+sizes.
This is focused cached validation, not a fresh frozen-release replay.

Kani001 rejected an unsupported CLI flag before compilation.005/006 timed out
at240s on giant dynamic byte selections; their logs/sources remain. They were
replaced by pointer+length obligations007/008, both passing in under2s. No
unchanged timeout rerun, cap increase or memory kill. Timeout RSS in GNU time
is launcher-only; aggregate cgroup peaks are separately recorded. Static
forbidden-proof/settings, full-statement comparison and git diff --check pass.

No file under crates/ or programs/ changed, so the ELF rebuild trigger did not
fire. Inherited pins, not reproduced:
default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4;
devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299;
Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548.
No keys,funds,features,parameters,wire format or release artifacts changed.
No binaries,objects,ELFs or archives committed. No push.

## Remaining obligations

The op4 arbitrary-operation gap is removed in this theorem chain under P6;
whole frozen2 parse still needs semanticRows27 and transcript Aligned on this
same proof. Batch/op5 Result/effects/authentication, later Q1/Q2/Claims and
checkpoint/FinishOps compatibility, native/runtime/oracle/query-history and
source-to-ELF integration remain as in the inherited handoffs. All original
SDK,std,allocator,runtime,extraction,oracle,child,history and P2Prime premises
remain. This task neither weakens them nor establishes the security headline.
