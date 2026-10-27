# Worker-kit audit

Work in progress. No release premise removed. Headline remains
`AspisR1.RPx_Deployed.deployed`; frozen3 and narrowed D188 unchanged.

The definition-by-definition inventory is [KSA_INVENTORY.md](KSA_INVENTORY.md),
with exact hashes, raw-emission comparisons and ambiguity candidates in
[KSA_inventory.json](KSA_inventory.json). Text identity and semantic fidelity
are separate checks. An unproved adapter is UNDETERMINED even if fixtures pass.

Known failures retained: predecessor-indexed `XRn_Join_mpow`,
`XRn_Join_qpow`, and the supplied `aspis_core.field.M31.inv`.
The canonical-input inverse-two disagreement is already proved by
`XSd_InverseCompare.mismatch`; exponent-two collapse by LPo's closed diagnostic.
These concern stand-ins; no shipped Rust or adopted-root defect follows.

Next: focused kernel checks, native frozen differential, theorem-dependency
inventory and import-isolated copies. Budget cap: 60 Lean, 10 Rust, 0 Kani;
one capped host scope at a time. No shipped source change or ELF rebuild.

## Focused kernel stage

`KSA_L002` passes `KSA_Checks`: inverse-two mismatch, generic exponent-two
collapse, multiplication-two = four, zero/P byte-decoding probes and explicit
carrier roundtrip. All seven top theorems print standard axioms only.
`KSA_L001` was a root-directory argument error before elaboration; corrected
only this job's invocation configuration, not the shared runner.

## Import collision resolved

`KSA_L003`–`KSA_L018`, then `KSA_L020`, compile the 17 private kit copies.
`KSA_L019` failed on three explicit root-qualified compact calls and an
unclosed generated noncomputable section; the replacement prefixes those
names and closes the scope. It is not a resource-failed rerun.
`KSA_isolation.json` checks reverse-name-transform byte equality for every
source. Bodies are unchanged, including the defects; these are isolation
copies, not replacements offered for adoption.

`KSA_L021` successfully co-imports the complete prefixed kit with the unchanged
`LPn_DotClosed`, Claims/Decode/Expand endpoints. `KSA.windows_roundtrip` and
`KSA.windows_next` prove exact carrier roundtrip and next-operation transport
for the two Windows owners; both print only `propext`. This resolves the
`Windows.noConfusion` collision without modifying either predecessor.
The co-import does not itself establish transport of all nominal kit carriers.

## New counterexamples and retained scopes

`KSA_L028` proves the WHOLE kit selected-mask result on zero coefficients,
explicit one and point `[1,0,...,0]`: first limb `1424173332`. Frozen native
Rust returns `708712922` (`KSA_R002`/`KSA_R004`). Both other limbs are zero.
The replacement is `AspisR1SelectedMaskProbe.state_only_hiding.state_only_selected_mask_value`,
used by adopted `AspisR1.FIp_SemanticArithmetic.mask`; retain the canonicality
conditions in `AspisR1.FIp_MaskValue.source`.

`KSA_L029`/`KSA_L034` prove a second exact source discrepancy, now directly
against emitted `FIo_Native...WideExact.mul_qm31`. Set the wide value's low
quartic component to `(1,0,1,0)`, high component zero, and the multiplier to
`(4294967295,0,4294967295,0)`. The kit returns low limbs
`(3,1,2147483645,0)`; the emitted body and frozen native return `(3,1,2,0)`.
The kit omits the emitted `canonical_qm31` call. Use the emitted body at
`lean/FIo_NativeFuns.lean:409`, not another handwritten adapter.
No claim that this noncanonical operand occurs in an actual verifier run.

`KSA_L031` proves exact complete same-input Dot.push transport to the emitted
FIo operation for arbitrary accumulator words and operands. Its two new roots
have standard axioms only. This is positive operation evidence, not a
whole-prepared-claim, query-history, adoption or artifact proof.

Failed attempts remain excluded: L025 hit the default heartbeat limit; its
broad simplification was replaced by the symbolic even-spine lemma L027 and
the focused result L028. L026 was an invalid monadic definitional simplification.
L032 needed explicit closed reduction for an irreducible byte operation; L034
passes. No timeout or memory failure was rerun unchanged or at a larger cap.

Rust R001 failed on four missing immutable fixture files; R002 adds precisely
those frozen files and passes. R003's direct use of native field arithmetic
on a noncanonical counterpart overflows under the explicitly recorded checked
optimized profile. This is NOT a source/emission/production defect claim.
R004 replaces ONLY the diagnostic counterpart with the kit's literal wrapping
arithmetic and passes, while native WideExact itself remains frozen. Every
run validates the offline resolved graph against the unchanged frozen lock.
