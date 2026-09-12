# Seed, salt, oracle and composition ledger

No numerical global privacy bound is assigned.

For one session, reserve the symbolic bound

`epsilon_total <= epsilon_seed + epsilon_salt + epsilon_commit +
epsilon_algebraic_bad + epsilon_fs_conflict + epsilon_sampler_abort +
epsilon_source`.

The terms are:

- `epsilon_seed`: distinguish or forbidden-query advantage when replacing
  the two private 32-byte seeds used by
  `generate_for_mask_nonce(proof_account_public_key)` with the ideal field
  and salt tapes. This is computational/ROM, not statistical uniformity over
  25,436 M31 coordinates.
- `epsilon_salt`: leaf-salt expansion failure or forbidden-query event,
  retaining one per-index salt shared by C1 and C2.
- `epsilon_commit`: lazy commitment/opening programming conflict in one
  coherent full-256-bit oracle table, with only the exact 208-bit commitment
  projection exposed as roots/frontiers.
- `epsilon_algebraic_bad`: histories/schedules for which the complete
  conditioned allowed-witness displacement is outside the remaining mask
  image. The consecutive-schedule diagnostic shows this term cannot be set to
  zero from universal raw rank. On tested valid transfers its separator is
  mask-seed invariant and contains the explicit term
  `170822063 / (recipient_value * change_value)`, in addition to a 384-row
  semantic-trace functional; whether the whole value is efficiently
  simulatable from the public statement remains open.
- `epsilon_fs_conflict`: an adaptively prior query fixes an answer the
  chronological simulator later needs to program. Cache hit, agreeing hit and
  conflicting hit are separate branches; no earlier answer is overwritten.
- `epsilon_sampler_abort`: first-hit exhaustion, duplicate/distinct OOD
  failures, q22 sampling failure, singular helper/denominator events and every
  externally visible proof-generation abort.
- `epsilon_source`: mismatch between the exact generated honest prover,
  serializer/application projection and their mathematical games.

The mask-limb exhaustion calculation `25471 / 2^496` belongs only inside a
proved ideal-word component of `epsilon_sampler_abort`. It is not a global
privacy estimate.

For `s` adaptive sessions, no multiplication or independence assumption is
made. A future theorem may apply a hybrid triangle/union bound only after
specifying the per-session adversary-query limits, fresh durable nonce
reservations, public-state evolution and the shared oracle history. Grinding
receives zero security credit.
