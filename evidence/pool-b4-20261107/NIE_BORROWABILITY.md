# Borrowability: OPEN

NHP K086 remains a retained liveness/abort finding on its stated valid Rust prestate. Production reachability is unproved. No soundness conclusion follows from it. No new inputs or transaction shapes are constructed here.

NIE_ACCESSORS.json pins all seven frozen Pool accessor locations and conservative direct callers: processor plan_fresh_program_pda, create_or_allocate_pda_with_rent, create_or_allocate_with_seed_with_rent, plan_vault_initialization; nullifier classify_nullifier_marker_account_v1; pair_forest process_pair_forest_deposit_with_runtime_v1; vault plan_legacy_withdrawal_transfer_from_identity_v1. The last site is custody/payment and must not be omitted. Static lexical call edges are candidates, not a cfg-resolved deployed graph certificate.

For EVERY site the exact outstanding fact is: on each reached deployed prefix, the same Rc data cell has no live exclusive guard, including any aliased account and any preceding child/CPI's post-state. Local absence of a RefMut declaration is insufficient. Native caller-prefix evidence with matched control AND model association are needed. No abort-prefix, independently selected state, free borrow-success premise, or unapproved runtime row is adopted.

## Exact unproved facts by site

| Site | Immediate prefix/caller gap | Status |
|---|---|---|
| nullifier.rs:208 / classifier | plan_nullifier_marker_consumption_v1 and plan_pair_forest_nullifier_marker_consumption_v1 must preserve the same marker data cell across encoding/address children; recheck must receive the actual post-System-CPI state with no surviving exclusive guard. Actual deployed parent layout/decoder/alias prefixes are not certified. | OPEN liveness |
| processor.rs:292 / plan_fresh_program_pda | Each of its 16 direct caller sites must derive the target-cell counter bounds after prior decoding, writes or CPI. The local mutually exclusive owner branches do not derive incoming borrowability. | OPEN liveness |
| processor.rs:332 / create_or_allocate_pda_with_rent | create_or_allocate_pda and create_nullifier_marker_if_needed_v1 must supply target-cell borrowability after payer/system validation and prior operations, including aliases. | OPEN liveness |
| processor.rs:398 / create_or_allocate_with_seed_with_rent | create_pair_forest_nullifier_marker_if_needed_v1 must establish same marker-cell borrowability at its selected creation arm; no owned-plan fact implies it. | OPEN liveness |
| processor.rs:504 / plan_vault_initialization | Both initialization parents must preserve vault-cell borrowability through preceding preparation/decoder calls and aliases. PDA/key checks alone do not establish it. | OPEN liveness |
| pair_forest.rs:1031 / deposit | Owned master/lane outputs do not by themselves certify counter cleanup in all preceding children on a current_page alias. Need root-to-cut alias/borrow frame. | OPEN liveness |
| vault.rs:485 / withdrawal planner | Mint scoped shared borrow ends before this site, but native/model Drop and all caller/alias entry frames must be established; the three direct caller contexts are not certified. | OPEN liveness |

The accessor requires shared acquisition room as well as absence of exclusivity. NIE_BorrowRelease makes the saturation bound explicit and proves its model necessity, without constructing an input or asserting production reachability. The inherited NGB MIR graph contains zero Pool edges; its verifier-only call graph cannot supply this missing Pool association. NIE_ACCESSORS is deliberately conservative rather than mislabelled as cfg-resolved reachability.

Native stage-1 input: K006/007 and K008..013 provide four actual recheck caller Result/alias cleanup/frame contexts with matched failures. These do not supply arbitrary full production caller prefixes. All copy bindings use the exact KMX file/patch; input/compiler/unwind failures remain excluded. L003 co-imports the model lemmas with the deployed headline; raw ax2/scan remains pending.
