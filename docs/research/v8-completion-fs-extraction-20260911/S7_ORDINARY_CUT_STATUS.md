# S7 pre-alpha concrete ordinary cut

Status: CHECKED local source-cut bridge; not an ordinary-event probability
theorem.

`FSV8S7PreAlphaConcreteOrdinaryCut.successful_prefix_constructs_cut` consumes
one successful execution of `selectedRelaxedThroughBeforeMarkerScript`.  It
constructs, from that execution rather than caller configuration, a single
cut containing:

- the canonically parsed same proof body;
- the dynamically produced semantic `z`;
- OOD result, gamma, kappa and tau at the pre-alpha boundary;
- the fallible `fromInputs` functional value and its exact provenance;
- the canonical fixed-field round-zero message; and
- the corresponding concrete compact coefficient vector.

`cut_false_claim_collision_mem_target` is the named degree-six consumer.  It
uses the cut's actual claim and response0, and leaves only the actual
word/covector reference family, false-discrepancy condition and collision as
explicit inputs.

## Exact remaining source producer

The selected pre-alpha result has no value of type
`List (Quad QM31 × Quad QM31)`, no finite family of those reference
coefficient vectors, and no theorem turning the accepted source relation
condition into the compact collision used by the consumer.  Those are the
missing source-produced received-word/covector and discrepancy bridges.
Putting them into `Cut` as fields would merely move the old
caller-supplied-target premise into a structure, so this leaf does not do so.

The next implementation theorem must derive the reference chunks from the
authenticated virtual quotient and carried structured covector at the exact
pre-alpha cut, then prove the actual ordinary discrepancy implies the
polynomial collision.  Only after that can the fresh/cached alpha-router law
consume this target.

## Focused check

On the NUC over Tailscale, with the pinned Lean 4.32.0 and existing olean
cache:

```text
lean -o FSV8S7PreAlphaConcreteOrdinaryCut.olean \
  FSV8S7PreAlphaConcreteOrdinaryCut.lean
```

Result: exit 0.  Promoted declarations report only `propext`,
`Classical.choice`, and `Quot.sound`.
