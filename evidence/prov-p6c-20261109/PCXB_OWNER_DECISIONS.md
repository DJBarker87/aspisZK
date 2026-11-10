# PCXB_ owner decisions (plain language)

Target not yet established. Nothing here changes a ledger row, trust row, RSL, the security contract or shipped source. These are recommendations; the decisions are the owner's.

## 1. The 24 cut modules with no recovered Rust source: reconstruct (R) or re-route (F)

All 24 are reached by the deployed_splitB cone and together serve rows of the ledger (per-module rows and cone constants: PCXB_NOSOURCE.md and .json). R means writing a Rust source from the Lean declarations and the contract, extracting it, proving equality, and running new Kani where a harness exists. The result is a source that behaves the same, not the original, so it ties the Lean text to a Rust file that never shipped. F means rewriting the bridge of each served row so it goes through a frozen-source emission, then re-auditing those rows.

Recommendation: F for the wide-fan-out modules (S1M31EmbeddingSourceV1 106 rows, CurrentWideMulCanonical 97, RPu_FIq_Native01 87, Native02 78), because an R-built source would be a new unverified artifact under rows that matter most; R only for the three S1Claim* modules and S1ValuesOwnedModelV1 (4 to 7 rows each) where the F rewrite costs more than the module is worth. Consequence of R: cheap and fast, but the cut equalities then prove "reconstructed text = gate", not "frozen source = gate", so the provenance gap is relabelled, not closed. Consequence of F: slower, touches closed rows, but ends with every served definition tied to the frozen tree. The 26 second-tier llbc-nearby cut modules (PCXB_SECOND_TIER_OPEN.json) were not worked and stay OPEN; they need the same R/F choice once the first tier is decided.

## 2. Hand-model trust-row classes (proposed text only: PCXB_TRUST_PROPOSALS.md)

* SDK type models (Pubkey, Hash, PubkeyError, ProgramError) and the core slice-iterator model (chunks_exact_mut): already pre-notified. No existing trust row covers them. Recommendation: accept as trust rows with the stated removal conditions.
* Option/Result, array/slice, num/ops helpers, discriminant helpers: recommendation: do not make trust rows; they are small closed proof tasks.
* array_from_fn_copy standing in for core::array::from_fn (23 blocked dependants): recommendation: prove the per-instantiation bridge rather than trust it; until then the 23 stay OPEN.
* Parametric records (Port3, Port4C, Port5Q2, AdapterRwModel; 34 definitions HAND_ADAPTED) and compact.OFF_*: recommendation: instantiate the records by the frozen items and prove equality; do not trust.
* Cross-crate constant encoding assumption (one line, PCXB_TRUST_PROPOSALS.md): recommendation: accept as one trust line for the constants not yet proved (STATE_ONLY_HIDING mask, Native07 selected_claim, Native13 COPY_PATTERNS), and remove it as each constant's own definition is shown equal.
* ShrAmt: verified by NPE_ (2026-11-10) for overflow-checks-off. Recommendation: record as a verified bridge with the restriction "never reuse for checked shifts with amounts wider than 32 bits"; residuals are the unchecked SBF-target build and the shared Lean usize width.
* Of the 601 externals with no gate definition, 502 resolve by a gate constant or hand model elsewhere, none is covered by an existing trust row, and at most 99 are genuinely unresolved (an upper bound). Recommendation: treat the 99 as open obligations, not as trust.

## 3. Gate definitions with NO_FROZEN_COUNTERPART

Eight gate-only helpers have no function in the frozen tree (list in PCXB_NONFROZEN.md; examples: decode_k_value, the r24 canonical multiplication closure). Their behaviour was proved on its own, but that is not an equality with anything frozen. If the deployed program does not call them they are dead weight; if it does, they are shipped logic with no frozen source. Recommendation: first check whether the cone reaches them from a closed row root; if it does, treat as a source-refinement obligation (not a cryptographic assumption); if not, drop them from the cone by re-routing. Consequence of leaving them: the corresponding rows cannot become provenance-clean.
