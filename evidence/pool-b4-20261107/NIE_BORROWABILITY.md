# Borrowability: OPEN

NHP K086 remains a retained liveness/abort finding on its stated valid Rust prestate. Production reachability is unproved. No soundness conclusion follows from it. No new inputs or transaction shapes are constructed here.

NIE_ACCESSORS.json pins all seven frozen Pool accessor locations and conservative direct callers: processor plan_fresh_program_pda, create_or_allocate_pda_with_rent, create_or_allocate_with_seed_with_rent, plan_vault_initialization; nullifier classify_nullifier_marker_account_v1; pair_forest process_pair_forest_deposit_with_runtime_v1; vault plan_legacy_withdrawal_transfer_from_identity_v1. The last site is custody/payment and must not be omitted. Static lexical call edges are candidates, not a cfg-resolved deployed graph certificate.

For EVERY site the exact outstanding fact is: on each reached deployed prefix, the same Rc data cell has no live exclusive guard, including any aliased account and any preceding child/CPI's post-state. Local absence of a RefMut declaration is insufficient. Native caller-prefix evidence with matched control AND model association are needed. No abort-prefix, independently selected state, free borrow-success premise, or unapproved runtime row is adopted.
