# Domain findings and limits

None of the small positive gates is promoted to an arbitrary accepted TX1.
The natural call-site domains in NBI1 remain binding.

- F331's0..8-byte gate covers the exact2-byte TX1 instruction class; it does
  not establish an arbitrary-length ASQ8 route. The separate exact2-byte gate
  and Lean instruction-shape laws retain this distinction.
- F330/F333/F344/F345 error gates return before actual verifier invocation.
  They cannot establish any accepted wrapper path. Release observer
  Option<fn> is not reached in these gates. No accepted observer-bearing gate
  receives credit or is renamed to evade K-2.
- F335 successful data views have length0/1. Actual TX1 snapshots have lengths
  58295/1880/1768. Applying these preflights as a full data-view bridge would
  impose an unsupported stronger precondition. Error gates cover Custom(u32),
  not every ProgramError variant; clone's full Result remains explicit in
  NCL_OwnedModels.data_error.
- F336 arbitrary usize Ok lengths cover the scalar length range, but native
  Custom(u32) errors are not all borrow/SDK errors. F337/F338 pointer identity
  gates use constructed typed OwnedAccounts; they do not identify the actual
  snapshot's arbitrary key/owner bytes or discharge ABI/runtime admission.
- F340's flags are arbitrary, but its other record fields are a constructed
  preflight class. F341 checks arbitrary flags/length/Custom errors with a
  fixed matching owner, plus a first-owner-byte distinction. This is not a
  full arbitrary32-byte owner/ProgramError/caller-carrier association.
- F342's native one-byte base case is NOT an arbitrary-suffix iteration law.
  The new Lean bounded model induction must not be mistaken for the missing
  native one-iteration association on the actual1768-byte prestate.
- F343's successful copy is one byte; wrong-length and real borrow-conflict
  branches use small AccountInfo values. The actual snapshots require full
  arbitrary-window value/frame, metadata, allocation and lifetime composition.
  Fixed key/owner/flags in these gates cannot be imposed on all actual callers.
  The optional arbitrary-metadata pair K049/K050 is unrun, not evidence.
- F332 short-buffer rejection is not successful1880-byte public decoding,
  Box ownership or preservation of the original public allocation.
- Full F094/F174/F328/F339/F344/F345 caller associations remain OPEN. No
  open child was replaced by an arbitrarily selected successful result.

The above domain mismatches are findings about insufficient proof interfaces,
not shipped-code vulnerabilities. Inputs, adversary, security metric, trust
items and the release target have not been restricted to fit these preflights.
