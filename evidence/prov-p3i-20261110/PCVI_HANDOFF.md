# PCVI_ HANDOFF: phase P3i

Target not yet established. No ledger row, trust row, RSL, contract or shipped source changed; no trust row added; nothing pushed or merged. Branch codex/pc-prov-p3i-20261110. Frozen source 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387. Host workspace /home/dombarker/project-offloads/codex-pc-prov-p3i-20261110/. 19 of 40 Lean scopes (PCVI_L001-L019), 0 of 6 extraction scopes, one at a time, caps 6G/8G unraised, swap 0, longest wall 180 s (L011, timeout), peak RSS 5.9 GiB. Exit-0 scopes: L002, L003, L004, L013 (definitions only), L019. Summary: PCVI_STATUS.json.

## Differences at a matching configuration
None found. The two configuration findings below are mismatches of the gate callees, not matching-configuration differences.

## Claims (exit-0 scope, axioms propext/Classical.choice/Quot.sound only, no sorry/axiom/native_decide, no raised heartbeats)
1. S1NativeCompact expand_semantic, _loop, _loop.body: CONDITIONAL_ON_BINDING (PRVEq_S1NativeCompactExpand_i1.lean, L002). For every ops, emission text with the external expand_values replaced by ops.expandValues equals the gate. Constants and row_shape fresh = gate; POINTS as ok fresh = gate (Result wrapper); CodecError read as the gate abbrev target. The P3g note that the emission row_shape is an if-chain was wrong: it is the same match text. Not shown: ops.expandValues = frozen compact.expand_values.
2. Port23PUSH update_residue_row and BatchedWeights.push: CONDITIONAL_ON_BINDING on the ArrayIntoIter parameter (PRVEq_Port23PUSH_Source_i1.lean, L003). Binding is the library into_iter (HM-B/HM-D).
3. NMT stage1_owned: CONDITIONAL_ON_BINDING over NMT_call_0..16 with the order table in the file header (PRVEq_NMT_stage1_owned_i1.lean, L004).
4. FIp NativeDots: four_dots_one_loop0_loop0.body, _loop0_loop0, _loop0.body, _loop0 EQUALITY_PROVED (PRVEq_RPz7_FIp_NativeDots_i9.lean, L019), plus fresh-local FIo helpers P, MAX_TERMS, Q.limbs, limbs_of, Q.from_limbs, checked_q, Dot.new, EbyKDot.new = FIo_Native.

## Findings that block items
* FIp four_dots_one, four_dots: the gate callees FIo_Native canonical.reduce and EbyKDot.push use wrapping operators; the ON emission is checked. rfl fails exactly there (L017). Both are overflow-free on the reachable domain but the lemmas are not proved. Same class would apply to NJA node_count (ON text over OFF gate loops, plus the hand NJA_well_formed vs emitted well_formed); not run.
* decode_pool_v1_pair_verified_afterstate_v1: the Aeneas emission clamps indentation at column 68, so the printed text is not a Lean term with the intended structure. PCVI_tokcheck.py: whitespace-insensitive tokens equal the gate (2250/2250). Textual evidence only; status OPEN (L005-L010).

## Not done
S1Claim* ReconstructedSource (ops-parameterised hand models; needs invented trait Rust and extraction), FIo x3, R72 secure_ood, binding upgrades, read_discriminant. See PCVI_REMAINING.json.

## Failed shapes
FIp: L011 (timeout 180 s, rfl on five definitions; never rerun unchanged, replaced by i2..i9), L012, L014, L015, L016, L017 (different shapes each). decode: L005-L010 (parse/layout). L001 (first expand_semantic file: parameter named compact shadowed the namespace; fixed in L002). L011 client was cut by my own shell timeout after submission; results were collected read-only from the host.
