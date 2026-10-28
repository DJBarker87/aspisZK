# Own input/script repairs

- Setup0: accidental global string replacement corrupted a Python string before
  the remote program parsed. Exit1 syntax error; no admission, copy or compiler
  launch. Replaced it by exact constant-binding substitution. Setup then passed.
- L002: deterministic whnf heartbeat timeout while elaborating the model cut
  assembly. No limit increase or unchanged rerun. Added local irreducibility
  for the large emitted tx1/prepare/suffix definitions; L003 elaborated in2.47s.
- L003: `subst split` selected the older equation to compact.SPLIT, leaving an
  opaque constant where the suffix requires literal10. Replaced it with
  `cases same` on the proved literal equality. The failed elaboration's
  sorryAx report is excluded; it is not accepted proof evidence.
- Forward drafts L005–L013: removed names that were externalized into Ops in
  the actual emitted source; explicitly unfolded the generated `uncurry`
  continuations; changed the final mutable-Vec return to its typed back-update
  expression; specified the constructor's actual E parameter. No source/body
  semantics, theorem statement or resource limit was weakened. L013 passed.
- Wrapper drafts L014–L016: added the existing WrapperLaws namespace and used
  the canonical CommittedCheckpoint.source owner. L016 passed unchanged in
  statement. All failed draft sorryAx outputs are excluded.
- Native configuration generation: an omitted Python json import caused a
  local NameError before any upload or prover invocation. Fixed the own input
  generator; no infrastructure changed and no proof was charged.
