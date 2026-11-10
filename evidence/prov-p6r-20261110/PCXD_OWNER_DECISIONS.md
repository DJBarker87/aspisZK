# PCXD_ owner decisions (plain language)

Target not yet established. Nothing here changes a ledger row, trust row, RSL, the security contract or shipped source. These are recommendations; the decisions are the owner's. This file updates PCXB_OWNER_DECISIONS.md with the PCXD_ numbers and the reach results.

## 1. The 24 cut modules with no recovered Rust source: reconstruct (R) or re-route (F)

Nothing moved. All 24 are still reached by the deployed_splitB cone; 20 modules are OPEN and 4 (RPu_FIq_CopyPrefix, Native02, Native03, Native13) have every reached definition equal to a reproduced text. That equality ties the reproduced text to the gate, not an archived crate to the frozen source, so it does not remove the question. R means writing a Rust source from the Lean declarations and the contract and proving equality; the result behaves the same but is a file that never shipped. F means rewriting the bridge of each served row so it goes through a frozen-source emission, then re-auditing those rows.

Recommendation, unchanged: F for the wide-fan-out modules (S1M31EmbeddingSourceV1 106 rows, CurrentWideMulCanonical 97, RPu_FIq_Native01 87, Native02 78), because an R-built source would be a new unverified artifact under the rows that matter most; R only for the three S1Claim* modules and S1ValuesOwnedModelV1 (4 to 7 rows each). The 26 second-tier cut modules were not worked and stay OPEN.

## 2. Hand-model trust-row classes (proposed text only: PCXD_TRUST_PROPOSALS.md)

P2i and P2j added no hand model, so the class texts do not change. The recommendations carry over:

* SDK type models (Pubkey, Hash, PubkeyError, ProgramError) and the core slice-iterator model (chunks_exact_mut): no existing trust row covers them. Accept as trust rows with the stated removal conditions.
* Option/Result, array/slice, num/ops and discriminant helpers: do not make trust rows; they are small closed proof tasks.
* array_from_fn_copy for core::array::from_fn (23 blocked dependants): prove the per-instantiation bridge; until then the 23 stay OPEN.
* Parametric records (Port3, Port4C, Port5Q2, AdapterRwModel; 33 HAND_ADAPTED definitions in the cone) and compact.OFF_*: instantiate by the frozen items and prove; do not trust.
* Cross-crate constant encoding assumption (one line): accept as one trust line for the constants not yet shown equal and remove it as each is.
* ShrAmt: verified by NPE_ for overflow-checks-off only. It now underlies 35 EQUALITY_PROVED and 2 EQUALITY_DOMAIN definitions. Record it as a verified bridge with the restriction "never reuse for checked shifts with amounts wider than 32 bits"; residuals are the unchecked SBF-target build and the shared Lean usize width.
* Of the 601 externals with no gate definition: 502 resolve by a gate constant or hand model elsewhere, none is covered by an existing trust row, and at most 99 are genuinely unresolved (class c, an upper bound). Treat the 99 as open obligations, not as trust.

## 3. Gate definitions with NO_FROZEN_COUNTERPART: now known to be reached

PCXC_ showed that all 8 gate-only definitions are reachable from AspisR1.TAS_FinalB.deployed_splitB at constant level and from at least one closed-row root (12 to 40 roots, 12 to 31 rows each). None is unreachable. The 8 are decode_k_value, the r23 bounded product and the r24 canonical multiplication closure family in AspisR72Sampler, candidate_claims.claims, and NJT_claims_ref. Reachability of a constant is not proof that the ELF runs the function, but it does mean the earlier option of "drop them if unreached" is closed: they are in the headline.

Two of them need a different reading from the rest. NJT_claims_ref is not an orphan: the reference function (sha256 2bf403f7...) is appended to the frozen r1_semantic.rs (c66eba53...) giving the scratch file e2a6d181..., and its re-extraction is byte-identical (PCWC_). It serves 12 closed rows. The AspisR72Sampler helpers come from an older field.rs; the M31.mul/CM31/QM31 equalities against the frozen text are proved (P3b), and P3b also proved the gate helper r23_product_u32_bounded equals a plain checked product; that is a fact about the gate, not an equality with a frozen definition.

Recommendation: treat the 8 as a source-refinement obligation, not a cryptographic assumption. For the six AspisR72Sampler and decode_k_value items, either show the deployed path never takes the helper (re-route) or extract the corresponding frozen function and prove equality. Consequence of leaving them: the 12 to 31 rows each serves cannot become provenance-clean.

## 4. The nine wrapping-closure definitions (new)

For nine definitions (three NNG verify_finish closures; six NJS batch_keys and sort_batch_keys functions) the gate carries wrapping on plain operators, while a checked-arithmetic emission of the Rust has plain `+`, `<<` and `-`. By the per-definition ruling the OFF emission is the correct basis and their OFF equalities count as EQUALITY_PROVED, with configuration OFF recorded. This is a ruling about what the gate models, not a finding that the Rust wraps: whether the frozen release build wraps is R22's question. Recommendation: keep the ruling, keep the nine counted separately, and let R22 decide checked versus wrapping for them. If the ruling is reversed they return to OPEN.

## 5. What the headline now supports

Of the 1707 definitions reached by deployed_splitB, 848 are EQUALITY_PROVED (694 in PCXB_), 256 are RECEIPTED (extraction receipts; configuration not re-derived), 554 are OPEN, and 49 are HAND_ADAPTED, EQUALITY_DOMAIN, CONDITIONAL_ON_BINDING or NO_FROZEN_COUNTERPART. 133 of the 209 modules still roll up OPEN (at least one OPEN, HAND_ADAPTED or NO_FROZEN_COUNTERPART definition). Recommendation: do not read the 163 clean rows as provenance-clean for release; they are clean only at definition level over annotated names, with hand-written names and the hand models above outside that. The next lever with the largest effect is the 325 definitions with no overflow-correct fresh emission, which needs extraction runs, not proof work.
