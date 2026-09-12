# Causal FS/source milestone, 2026-09-12

This checkpoint advances two deterministic interfaces needed by the global
soundness proof.  It does not establish a random-oracle probability law,
payment extraction, or global 100-bit security.

## Checked results

- `FSNonzeroSqueezeExposure.lean` proves that the first literal squeeze of a
  positive-fuel nonzero-QM31 sampler remains in the final chronological log,
  including decoded-zero retries, errors and exhaustion.  Freshness and
  uniformity are deliberately not conclusions.
- `FSV7FourBlockWordBridge.lean` proves exact decoder compatibility between
  the current masked four-block word stream and the deployed V7 Tag-73 raw
  decoder.  Accepted limbs, rejection, attempt counts and `wordsUsed` agree;
  the unread suffix is masked explicitly.
- `CausalSourcePolynomialTrace.lean` constructs a reference semantic trace
  from chronological restrictions of the actual source polynomial.  Its
  endpoint is the final restriction's evaluation.  This avoids the false
  substitution of a Boolean-table MLE at off-domain challenges.
- `FSV8FreshTapeBudget.lean` proves that the composed source-to-OOD-to-gamma
  script consumes at most its finite static call budget of fresh tape answers
  from the empty lazy oracle.  This is the deterministic resource bridge to
  the older V7 finite-tape probability work, not the probability theorem.

All three focused leaves passed pinned Lean 4.32.0 checks on the NUC under
capped systemd scopes with zero swap and only the standard axioms recorded in
their machine reports.

## Exact remaining seams

1. Locate the first exposure of every live sampler request in the global
   adversarial oracle history and couple the resulting fresh-answer sequence
   to the V7 finite uniform tape.  A cache hit at verifier call time is not by
   itself a bad event: its first exposure may have occurred earlier.
2. Connect lazy one-to-four-block live consumption and final transcript state
   to the checked four-block decoder result.
3. Instantiate the causal source-polynomial interface with the selected
   pair-forest `payment_terminal` implementation and prove the literal callback
   correspondence.
4. Compose those facts with same-body authentication and an allowed-access
   checked-payment extractor.  Until then, the existing numerical bounds are
   conditional local screens.

The proof body and verifier grammar are unchanged by this checkpoint.
