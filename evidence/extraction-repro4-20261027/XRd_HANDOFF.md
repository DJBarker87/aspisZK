# XRd selector-only extraction continuation

**Target not yet established. D188-P2/L187 and release/cohort association remain
open.** Actual checkout branch codex/cx-extraction-repro4-20261027; no push/merge.
Only this evidence directory changed. No shipped source, ledger, contract,
session A live worktree/candidate, other worker prefix, wallet/key or ELF changed.

## Established artifact and new blockers

Approved selector-only Charon lowering of the identical 7978-file release
snapshot at 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387 succeeded. Identical
rebuilt tools, features, preset and MIR; no source/translator/library patch.
Full command/environment: XRd_release_candidate_charon_command.json.
Second pinned release LLBC:
80465ea37dd7c3c5becdd9c413d745ae076adf5b193067e8618d58db075c43e5,
12,864,440 bytes, has_errors=false, retained on host beside original 0814e4ec….
Required bodies omitted by the old artifact are now structured LLBC bodies;
XRd_llbc_inventory.json records ALL function names/body hashes. This closes
body availability at the LLBC layer, not a Lean association or top premise.

The complete requested Lean kit cannot be emitted by pinned Aeneas:
- XRd_002: checkpoint “Could not match the contexts”, verifier.rs:330:4–330:55
  (`for root in &p.roots`), InterpJoin.ml:2209. XRd_003 removes abort-on-error
  to collect independent successes, but the same exception remains fatal.
- XRd_004 lowers an INCOMPLETE independent subkit with checkpoint additionally
  opaque (370b8a0a…,11,949,563 bytes). XRd_005 then exposes prepared_claim's
  uncaught Not_found at InterpReduceCollapse.ml:1991, the abstraction-ID map
  lookup while remapping a shared-borrow sequence.
- XRd_006 captures the detailed collapse contexts and full error stack. It
  confirms y1/g shared borrows and the parts-array mutable write at the failing
  loop fixed-point context. No concrete Rust span is supplied for this exception;
  no source defect or mathematical counterexample is inferred.

All FOUR Aeneas runs exit2 before emitting ANY Types/Funs. The four mandated
leaves remain opaque. The checkpoint split is explicitly incomplete, not a
fifth approved release leaf or an association proof. No LLBC was masked,
rewritten or supplied to a modified translator.

XRd_kit.json pins artifacts/coverage. XRd_Diff.md and XRd_declaration_diff.json
retain all 45 coherent producer Types and 87 Funs as UNPROVED; a complete fresh
release declaration diff is unavailable. XRd_OBLIGATIONS.md lists exact
remaining scratch/gamma/kappa/cache/count/accepted-path/effect interfaces,
ledger families and sizes. No XRd_Association.lean or concrete typed Props are
fabricated against missing declarations (common rule4). No new Lean theorem
or #print axioms result. XRc's isolated error-carrier theorem is reused only
within its original scope, without an unchanged compile rerun.

## Validation, budget and resources

**Used 6/6 combined Charon/Aeneas (2 Charon,4 Aeneas),0/100 Lean,0/0 Kani.**
Extraction budget exhausted: no further extraction/proof work launched.
All six attempts are terminal; all reservations admitted, zero retries.
One own scope at a time; MemoryHigh6G/MemoryMax8G/Swap0/Tasks64; optimized Rust,
-j1, pinned toolchain and exact commands. No timeout, memory kill or cap raise.
No infrastructure was repaired or rewritten; copied S2W runner hash matches.
Each receipt has target/command, source revision/hash, dependency pins,
exit, wall, peakRSS, swaps, scope, limits and N/A theorem-axiom result.
XRd_Verification.json aggregates them. Max RSS549976KiB, all swaps0.

XRd_006's complete debug log (about61MiB) remains on host; its exact path/hash/
size is XRd_HostAudit.json. XRd_006_final_context.log commits its final2000
lines, including the final contexts and complete Not_found stack. No large
log/binary/LLBC/object/cache is copied into this worktree. Final host audit
rechecks all five inherited tools/artifacts and 7978 release source files,
all unchanged, and both new LLBC hashes. Own Cargo cache is removed; pinned
LLBC and diagnostic evidence are retained. No other job/cache is touched.

## Actual top, recount and non-vacuity

Before/after complete AspisR1.Rc10_Top.deployed sources are byte-identical,
SHA256 c5c85966b83fbaf24626724fe9becdef92214389fb4286d6ba0d304f486e1527,
retained as XRd_Top.BEFORE/AFTER.lean.txt. Ledger unchanged. Ledger-method
removed/added/changed0/0/0; delta T0/P0/G0/C0, preserving shared witnesses,
quantified atomic families and alias L185=L159; no fresh absolute recount.
No binder, carrier, failure event, conclusion, trust item or metric changed.
Frozen3, approved game and RuntimePersistence remain adopted. No same-witness
joint security-game inhabitant is constructed; structured LLBC is not whole-top
non-vacuity. Formatter reachability/axioms and coherent whole-top replay are
not newly established.

No shipped-file change means no three-ELF rebuild trigger. Inherited pins,
not newly reproduced: default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4;
devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299;
Pool121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548.

Next deliverable needs a separately approved extraction strategy for checkpoint
and prepared_claim, preserving this exact source/tool/failure evidence; then
complete Types/Funs and the concrete association projections in the requested
order. Current constraints forbid patching the translator, substituting a
library, or editing frozen source. No approval is inferred or requested here.
