# Native P6 ledger delta

Local proof selection: `NP6_ParsedPair.accepted_pair_unified`, backed by `NP6_SOURCE_CERTIFICATE.md`. Apply the binding 2026-10-26 native Vec/Box ruling, with no additional trust. Global S2 remains OPEN; the release target is not established.

| Row | Before | After in this selected cone |
|---|---|---|
| L174 initial/pending native instance | Content constructor theorems lack concrete Copy/Std/allocator/runtime interpretation. | Removed: safe extracted constructors use existing D188/Allocator/runtime boundaries; actual selected Clone/fill and constructor calls yield initial/pending Contents on the SAME TX1 run. No successful constructor premise is added. |
| L177 Claims native std slots | Free reserve/intoBox slots and mapError/boxArray value models; native unsafe ownership/abort/effects open. | Removed: source-pinned P6 composition equates complete native Claims and owned extracted reference, including Result, live contents and relevant frame/ownership/cleanup. Safe standard slots are fixed and their content/error laws proved. Allocator response stays under the existing Allocator item. |
| L179 library/native frame | Installed content/library joins lack actual native std/runtime/ABI/source dictionary association. | Removed for this selected dictionary: D188's safe standard model plus the P6 unsafe-source bridge supplies the concrete association. The original runtime/SDK/ABI/extraction fields stay explicit. No arbitrary Ops/native dictionary interpretation is asserted. |

Delta: **3 must-prove rows removed, 0 added, 0 new or widened trust items.** This prefix-only delivery provides the delta for the lead; it does not modify the shared ledger or another worker's modules. The lead can adopt the selected module and these receipts without treating the old unrestricted-slot theorem as a newly proved arbitrary native instance.

## Before and after statements

Before, original `T2Nat_NativePair.accepted_pair_unified` quantifies over `claimsStd : ClaimsUnrolledFinish.StdCalls` and requires AeneasExtraction for the exact installed dictionary, original wrapper successes, copy/allocator/runtime/SDK/hash and other owner premises. Its output fixes f/s/cuts, the accepted execution, source joins and success-conditioned marks. Its frozen hash remains unchanged.

After, `NP6_ParsedPair.accepted_pair_unified` retains all those premises and conclusions with the Claims slot argument concretely instantiated to `NP6_StdModel.calls claimsReservation`. It quantifies over the allocator outcome, not an assumed successful Claims/constructor return. Additional conclusions are `NP6_Constructors.Contents run.initial run.pending`, `NP6_ClaimsRun.Content` and `NP6_ParsedClaims.Content` on the same witnesses. The actual parse implies the source record's3717-byte width, the original success implies allocator success, and all decoder/constructor content equations are outputs.

This specialization by itself would remove ZERO native premises: that was accurately recorded in Stage2. The native premise removal is supplied by the independently checked whole-caller characterization gates, exact Result composition, frame/ownership/cleanup gates and retained selected extraction. It is a concrete implementation instance, not a container bundling the old assumptions or a generic join accepting the desired equality as a hypothesis. Rust gate hypotheses are not silently promoted to Lean axioms; the cross-tool source certificate identifies each concrete premise and its checker.

Quantifiers over adversarial parsed bytes are unrestricted. The accepted-pair witnesses, public/cut carriers, query order, failure event, crypto assumptions and original outer success restrictions are unchanged. Result composition covers successful output and decoder rejection at this reached helper cut. The shared allocator error branch is accounted for before decoding under the existing Allocator item; Kani's unsupported custom-allocator profile is explicitly excluded. No full outer failure/divergence or global security experiment is inferred from this local helper result.

## Non-vacuity and remaining premises

The real native parser fixture R002 reaches nonzero matching Claims, K006 reaches full construction and late error, and the checked local constructor witness returns initial/pending values. These establish local reachability, not a deployed accepted cryptographic spend. The strengthened joint theorem introduces no new acceptance hypothesis or impossible condition.

Retained: the exact original AeneasExtraction and stage/digest association, RuntimeEntrypointAdmission, S2TrustedSdkBorrow, TrustedStd copy, Allocator, P1/runtime syscall, wrapper success equations, session-owner preparation/query/geometric and other cone obligations, outer rejected-prefix/effect accounting and all security/probability hypotheses. Eliminating these three std/native instance rows does not eliminate those distinct premises. Session A and Hist_/DrvC_/RawJ_ candidate modules were untouched.
