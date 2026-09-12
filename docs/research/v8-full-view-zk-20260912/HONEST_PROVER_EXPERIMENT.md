# Honest entropy-backed prover experiment

## Scope

The real experiment covers one repaired positive private transfer under the
fixed profile, release and descriptor in `SOURCE_MANIFEST.json`. Withdrawal,
wallet-encryption privacy, network anonymity, timing/physical side channels
and adaptive secret-key compromise are excluded.

Public input/allowed leakage is the full statement and afterstate, profile and
release identifiers, proof/account framing, output commitments and
nullifiers, serialized lengths, public attempt identifier, and the terminal
success/opaque-failure status described in `PUBLIC_VIEW.md`.

## Real experiment

1. Accept a public statement `x` and a valid private-transfer witness `w`.
2. Create the proof account first and use its public key as the unique public
   mask nonce, matching the deployed API contract. Call
   `StateOnlyAttemptSecrets::generate_for_mask_nonce()`, which obtains 64
   OS-random bytes and separates the field-mask entropy and leaf-salt seed;
   all-zero private components are rejected. The alternative 96-byte
   `generate()` API belongs to experiments where the nonce is not preselected
   by the proof-account key and is not selected for this adapter.
3. Durably reserve that proof-account-derived public nonce before deriving private material.
   A reservation is never reused after success, retry, abort or process
   failure.
4. Use the existing pool-pair-forest mask-material, D and per-leaf-salt
   derivation APIs. Preserve the single salt per leaf shared by C1 and C2.
5. Run the pinned repaired q22 prover algorithm and canonical serializer.
   Every abort/retry remains part of the result distribution. Until a matching
   q22 publication gate is designed and separately reviewed, this experiment
   does not add one.
6. Return the public event projection only. The adversary shares one coherent
   full-256-bit random-oracle table with the prover and receives answers to its
   own adaptively chosen queries. Commitment outputs use the exact 208-bit
   projection of that same table.

The archived performance demonstration is not this experiment: it uses fixed
repeated-byte secrets and `InMemoryStateOnlyMaskNonceStore`.

## Session rule

The first theorem target is one session with fresh secrets and an explicit
adversary query bound. Multi-session composition must retain one shared oracle,
fresh durable attempt reservations, public state evolution and all visible
failures. It is not inherited from the one-session target.

## Open source adapter

A production-quality adapter must still connect steps 2--6 to the generated
   q22 source and serializer, and confirm where the proof-account nonce is
   exposed in the application envelope. The adapter must not redefine the literal prover to
equal a model. It must expose reservation failure and proof-generation aborts
without leaking retry count, selector, rank reason, entropy error, secret
material or partial candidates.
