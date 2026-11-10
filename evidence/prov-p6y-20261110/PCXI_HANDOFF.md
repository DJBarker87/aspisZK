# PCXI_ handoff (job pc-prov-p6y)

Claim: of the 183 RECEIPTED cone definitions without pin-equal evidence, 64 are PIN_EQUAL, 79 TEXT_DIFFERS, 40 NOT_REDERIVABLE (counted OPEN). SETTLED 993 -> 1057, NOT SETTLED 649 -> 585 (OPEN 466 + TEXT_DIFFERS 79 + NOT_REDERIVABLE 40). Evidence: PCXI_RECEIPTS.json (per definition), PCXI_SUMMARY.md.
Ran: source work only (bash PCXI_compare.sh, ~60 s, then bash PCXI_finalize.sh). 0 Lean, 0 extraction, 0 Kani scopes.
Limits: PIN_EQUAL is Rust-text plus configuration provenance; the gate-module to emitted-file link is still the PCO candidate sha. External-crate dependency items were not compared. PIN_EQUAL modules: Qm31 probe (6 Funs, 3 Types), RowShape 4, WithdrawalValidation 8, NCX 8, NEI_FourWrapper 1, NEV Types 3, NGD_SlotRef 1, Op3I_Source 24, Port3_NativeQueryBody 6.
Next: source/receipt for NDH, NEA, NCO, Op4P, Ports, SAQ, NKV (see reasons in records); optional fresh = gate check for modules at COVERED_DIFFERS.
Target not yet established.
