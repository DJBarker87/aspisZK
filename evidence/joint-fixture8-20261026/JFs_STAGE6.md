# Complete native ASF8 public decoder

`JFs_PublicDecode.source` (073) proves the actual emitted full decoder returns
`JFs_PublicValue.value` on the SAME retained1880-byte physical public input.
`JFs_PublicValidation.source` (069) proves the exact native enclosing validator
accepts that value, including payment encoder, all binding comparisons, native
output lane3 and the successful late encoder. No child-success,metadata,
canonicality,header,root or validator-success premise remains in these theorems.

The repeated rejected outer composition drafts060–068 are retained. They
isolated the actual Aeneas `uncurry` let-pattern continuation and the exact
selected nullifier carrier; no implementation/model was changed. 068 had
standard axioms but an extra tactic after the goal closed;069 removes it.
071 similarly had an extra tactic;072 is accepted. No timeout or memory kill.

Budget through074:74/100 Lean;0/10 Kani. Standard axioms only on accepted roots.
This is concrete public decoder/validator non-vacuity, not TX1/TX2 native
acceptance, not the full joint game and not JFs_Fixture.inhabited. Top premise
delta remains0T/0P/0G/0C. Next: semantic serializer binding/initializer.
