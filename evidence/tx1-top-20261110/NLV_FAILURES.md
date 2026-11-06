# Retained failures

No failure earns row credit. No timeout/cap was raised.

- L002: own prelaunch input error, missing NLN_TX1_081 object in inherited path;
  no scope. Added authoritative ledger23 NLO paths read-only, L003 passed.
- L004: own Lean syntax/ambiguous bind draft. Corrected explicit namespaces
  and indentation, L005 passed with standard axioms.
- Client serialization refusal before L006: guard prevented a second scope;
  waited for L005 and submitted L006 once.
- L022: prepare continuation needed explicit splitting of the returned pair
  and its inner Result; L023 corrects that proof, preserving the SAME scratch.
- L030: reserved identifier `local` in proposed physical-state helper;
  renamed the binder, L031 passed.
- L034: direct whole-body rfl failed; no equality admitted.
- L035: broad whole-body unfolding/congruence hit the default heartbeat limit.
  RETIRED. No unchanged replay or limit increase. Replacement splits the
  emission definitions, pair-elimination lemma, individual suffix transports,
  and focused structural source normalization. No recurrence normalization.
