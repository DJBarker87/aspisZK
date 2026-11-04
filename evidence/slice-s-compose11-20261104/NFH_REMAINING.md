# Remaining scanner obligations

The seven-root target remains NOT ESTABLISHED. The sole OPEN slice member is
programs/r1-cost-probe/src/r1_pool_adapter.rs::scan_proof_buffer, TX2:226.
No new row, edge or root closes in NFH_.

1. Runtime value and frame: the actual comparison reaches sol_memcmp_ through
compiler-builtins memcmp, not a visible byte loop. Its688-byte zero law and state
frame are unproved/unadopted. See NFH_COMPARISON_FINDING.md for the exact symbol,
ELF addresses, smallest proposed trust item and alternative outside-slice packet.
This requires a runtime implementation proof/association or explicit owner
adoption. More verifier-program Kani checks cannot inspect a body absent from
the program. A host memcmp loop is a different implementation. An oracle can
check argument/reply forwarding but cannot constrain the missing reply truth;
NFD's suffix support already performs that kind of forwarding observation.
2. SAME-buffer native association: use the eventual runtime certificate on the
actual encoded output/header allocations and its i32 output slot, then identify
the caller's zero/nonzero test with NEU_EqualityLoop. Static instruction checks
in NFH_ are inspection SUPPORT ONLY, with mutation controls; they are not Kani
certificates or a new PhysicalInterpretation assumption. No whole-buffer
symbolic equality harness was submitted or repeated.
3. Only after that association, issue the three call-domain certificates:
   scan_proof_buffer -> Variant::tag;
   scan_proof_buffer -> decode_pool_v1_pair_verified_afterstate_v1;
   scan_proof_buffer -> encode_pool_v1_pair_verified_afterstate_v1.
Their child bridges and NFD local supports are reused. Binding job order requires
nativeEqualityBridge first; these three are explicitly UNISSUED here, and all
three edges stay OPEN. Primitive obligations external:TX2:226:3 through:12 also
remain unissued in the scanner's root packet; no evidence flag closes them.
4. Issue the scanner root certificate, replay the additive validator, then run
the full slice-S NEP_Driver audit with ax2 fixtures/controls. The conditional
NFD model theorem is not this root certificate. The conditional audit trigger
(root closure) has not fired. The overall release still needs its coherent cold
replay and all non-slice obligations.

## Whole-budget stop audit (under80%)

Budget used:0/100 Kani,6/50 Lean,0/5 extraction. NFH_L004/L005 are accepted support modules;L006 audits the final import; L001–003 are excluded changed-source elaboration failures. No
Kani/extraction timeout, memory kill, or unchanged rerun occurred.

Member-by-member: there is EXACTLY ONE assigned OPEN member, scan_proof_buffer.
Its missing fact is the above runtime law. That implementation is outside the
slice's function list; the job expressly directs an exact named trust proposal
or outside-slice packet when the reached body is unavailable. Both are supplied.
There are no independent remaining assigned members to move to. Decoder, encoder
and tag are already CLOSED callees; their scanner edges are ordered after this
association, not new members eligible for horizontal work. Existing length,
header, decoder/Box, candidate projection, suffix, byte step and symbolic
induction supports are already complete. NFH additionally proves the explicit
value-law interface sufficient and necessary, with an opaque-reply countermodel,
and the explicit conditional688-domain completion.
No independent Lean-only obligation is identified: none of those proofs can
establish the runtime implementation fact. No extraction run can extract an
undefined ELF symbol's implementation. Spending the remaining allowance on
repeated support, invented loops, unrelated members or an assumed syscall zero
law would earn no composed credit and would violate the assigned scope/method.

No trust is adopted and no metric, carrier, protocol or release target is
weakened. RuntimeMemcmp688Zero remains a PROPOSAL requiring a ruling; neither
RuntimeReturnData(ab) nor hash realization supplies it.
