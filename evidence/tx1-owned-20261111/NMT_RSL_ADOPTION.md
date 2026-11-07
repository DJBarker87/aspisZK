# Canonical RowSpec adoption for the resumed run

The exact targets are `RSL.TX1_087.RowSpec_087`, `RSL.TX1_094.RowSpec_094`,
`RSL.TX1_328.RowSpec_328`, and `RSL.TX1_345.RowSpec_345` from the lead package.
NMT_RSL_PROVENANCE.json records source hashes; NMT_RSL_* copies change ONLY
import module names. L061–L069 compile the complete dependency chain on the
pinned coherent host. These are specifications, not emitted implementation
proofs, and no row is promoted.

The prior `NMT_RowSpec_087/094` are no longer proposed target statements. They
used an independent total-producer/returning-world and ordered-attempt carrier,
including a two-backend runtime projection clause at094. No equivalence to the
canonical RSL semantics was proved. The resumed target uses the canonical
`Obs`/`Env`/`Event`, exact `Except` and abort-prefix semantics, and its domains
verbatim. In particular094 has ONLY observer=None and publicDom;345 has no
own-input clause. The old backend projection is not added to either target.
Canonical087 keeps returned scratch on every Rust Result; stopped arms have
no post-state. No allocator-internal state is introduced.

At345 the parent state stores the complete original program/accounts/data,
ambient world and effect prefix. Its selected-account extension retains this
state. The first CLOSED339 call uses the literal three-account array; both
CLOSED340 occurrences have no domain.341 and335 have restricted native
snapshot-error packets, so the local modules expose their exact domains and
separately retain the existing generic emitted/std clone laws. Those generic
laws preserve arbitrary ProgramError payloads; they are source/library support,
not an unannounced expanded Kani certificate. All eventual physical uses must
retain the existing std/extraction interpretation.

An arbitrary owned account can claim length1768 while its Vec has another
extent. Thus341 success alone does not imply the342 bound4096. The new symbolic
zero increment/induction uses the actual Aeneas slice capacity instead. No
relation between unrelated account fields, or a publicDom conclusion, is
smuggled into345's domain. Exact caller-domain installations and complete
observable composition remain required before calling the fold complete.
