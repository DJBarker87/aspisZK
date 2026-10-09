# Relation consumption constructs the causal word

`SameBodyConsumeConstructsWord.assemble_roundtrip` proves that the canonical
early fields, four six-element response rows and final256 projection reassemble
any 697-field word exactly.

`consume_success_constructs_word` then uses the equalities produced by a
successful `SameBodyRelation.consume` run to prove that the submitted word is
the realised serialization of the legal staged strategy at the actual tau,
alpha0, query schedule, rho and later coins. This replaces an independently
supplied 697-field equality with the checks performed by the consumer.

`SameBodySourceFromConsumption.completeFromConsumption` installs that result
in the dense source producer. Its ordinary claim and terminal covector remain
the already constructed source values. A legal pre-tau strategy and actual
consumer success remain source-execution obligations; neither terminal
acceptance nor a probability conclusion is embedded in the interface.

Focused NUC checks used pinned Lean 4.32 and the private base/overlay union
cache; dependency sources were not rebuilt:

- `SameBodyConsumeConstructsWord.lean`: exit 0, wall 1.63 seconds, peak RSS
  3,369,524 KiB, swap 0; source
  `7ad3dd7aedf7d531b8f5feff98959466d17f35e9da0890ce631020d683fa9738`,
  OLean `95df298ef7723b205330f1c6375d4c8ec0e2e6ab554e98d22b79300f7eb18aa2`.
- `SameBodySourceFromConsumption.lean`: exit 0, wall 2.88 seconds, peak RSS
  6,769,016 KiB, swap 0; source
  `56ca6859a3bc1896b9560f31aca9206fe6b6161171db0f7c78804cf6e8632606`,
  OLean `14353ed1a379815757bb6352b18cdbfa6859ed99b9a02779a2f2869e7a35ac5f`.

All promoted theorems print only `propext`, `Classical.choice` and
`Quot.sound` (the generic roundtrip does not require `Classical.choice`). No
protocol, body, acceptance, security ledger or CU claim changed.
