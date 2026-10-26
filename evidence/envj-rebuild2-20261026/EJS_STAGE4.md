# Recursive dependency and package recovery

The original frontier provided 234 unique exact source hashes; recursive receipt and source-graph resolution added 637. Historical git traversal resolved eleven more exact CompPoly sources. The historical environment inventory pins upstream CompPoly revision 4165a87dd9a9ede48ee4dc5b4fe825604b8bb932. Its immutable source archive matches all eleven independently recorded hashes exactly. Seventy-six further needed ancestor sources match repository git blobs in the same historical source snapshot byte-for-byte. Only this needed chain is staged; no archive/binary is committed and no original unresolved source hash is substituted.

The dependency parser now recognizes Lean 4.32 `import all M`; `all` was incorrectly treated as a missing module. This is an EJS adapter repair only, with no proof source edit. Valid reuse aliases remain protected from fallback overwrite.

31435 stopped on a missing transitive wrapper object. When the object became available, the launcher correctly refused the unchanged old fingerprint before Lean started (EJS_refusal-31436.json). The new fingerprint records the actual transitive object/source hashes. The repaired-input retry succeeds; subsequent ProverCommit modules proceed. Actual compiler IDs remain contiguous; guard refusals do not count as compiler attempts.

The interim integrity audit found zero object-hash mismatches and one changed shared source: J/sources/R1Z/PrivacyR1HeadlineV2.lean. It is preserved rather than overwritten or adopted. Final source/object checks and exact remaining states will be collected after the bounded compiler queue stops.

No shipped source changed, no security premise removed, no ELF rebuild trigger, no Kani or Rust. The actual Rc2 top source and static ledger remain unchanged. Target not yet established.
