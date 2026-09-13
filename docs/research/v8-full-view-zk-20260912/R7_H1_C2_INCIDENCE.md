# R7 H1 incidence and fixed-observation result

Date: 2026-09-13.

Status: **Tickets A and B complete as a conditional fixed-observation result;
no full-view privacy or publication claim**.

## Source-instantiated helper identity

Let `D : QM31^136 -> QM31^1024` be the public signed incidence map obtained
from `build_pool_v1_pair_forest_copy_registry_v1()`: each registry link has
`+1` at its producer row and `-1` at its consumer row. The source inventory is
136 links, schedule fingerprint `0x480809b836778dc6`, 214 active rows, 78
connected components, and 810 inactive rows. Padding uses pivot row 0 and the
809 directions `e_r - e_0` for the other inactive rows.

For either honest compiler entry point, successful `finish` requires every
constraint residual to vanish. `append_tuple_equal` contributes all 16
residuals

```text
weight * (producer_limb - consumer_limb)
```

for every registry link. Consequently, on every nonzero-weight link, the
complete producer and consumer tuples are equal. This conclusion uses the
literal tuple residuals; it is not inferred from compressed equality.
`merge_pool_v1_pair_forest_trace_banks_v1` binds the late source rows into the
semantic C1 trace read by the registry. `pool_v1_pair_forest_copy_rows_v1`
then compresses those same tuples with the public tag, public append index and
actual public link weight. Finally `build_copy_logup_helper` skips zero weights
and either returns an explicit active-pole error or adds the corresponding
signed inverse at the producer and consumer rows.

Therefore, for a successfully validated honest trace and a pole-free `chi`,

```text
H1_unpadded = D a(w, lambda, chi),
H1_padded   = D a(w, lambda, chi) + P u.
```

The coefficient for link `e` is its actual public weight divided by
`chi - compressed_tuple_e`. It may depend nonlinearly on the witness,
`lambda`, and `chi`; the incidence conclusion does not assume coefficient
linearity. The 136-column `D` is a safe public overapproximation when a public
weight is zero. Slots, inactive rows, append-index weights, and pole failures
remain explicit premises.

The actual-compiler duplicate-selection regression checks all 1024 rows. Edge
19 (`InputSelectedSide`) has tag `0x43000013`, producer row 913 and consumer
row 1017, and the observed helper difference is exactly

```text
delta * (e_913 - e_1017),
delta = 1/(chi - tag - lambda) - 1/(chi - tag).
```

The test's diagnostic `lambda` in CM31 and `chi` outside CM31 only avoid poles;
they do not alter the protocol challenge domain. Its `lambda = 0` control has
zero difference.

## Fixed linear observation theorem

For a fixed public linear observation `L`, put `M = L P` and `T = L D`. The
actual circle encoder and the existing affine certifier produce and directly
verify a correction `C` with `M C = T` for the known q4/q6 pair and all three
22-query controls (consecutive, spread by 11,915, and the scattered q4/q6
schedule). Each has correction rank `4q`. C2 encoding is verified to be the
same M31 twiddle encoding independently on each of the four QM31 coordinates.

The Lean endpoint `fixed_helper_observation_uniform` combines:

1. complete active producer/consumer tuple matching and pole freedom;
2. the source incidence identity;
3. fixed-linear coverage `(L.comp P).comp C = L.comp incidenceMap`; and
4. a fresh uniform conditional law for the 809-dimensional pad `u`.

It concludes that the observed padded helper has the same law as `L(Pu)`,
independent of the witness. This is a view theorem for one correctly fixed
linear block. It neither supplies the fresh-pad premise nor constructs a
valid witness-free prover trace.

The missing premise must come from a source-instantiated ideal-expander and
prefix/commitment hybrid: conditioned on the already exposed C1 history and a
coherent random-oracle history, the unused H1 pad coordinates must still have
the stated uniform law. R7 does not assume that result by name.

## 84/87 point projection

The literal projection `v[271 + (i/28)*29 + i%28]`, for `i = 0..83`, is
injective and selects 84 of the 87 serialized point fields. It retains all H1
and G entries and omits exactly the three D entries 299, 328 and 357. Those D
entries remain public serialized transcript fields; the projection does not
remove them from the privacy view or change the proof format.

## Gate separation

- The existing C1 q4/q6 same-public failure remains a mandatory failure and is
  unchanged. H1 incidence coverage does not repair it.
- The fixed-block H1 result is conditional on fixed `L`, source validity,
  pole freedom, coverage and fresh conditional pad coins.
- Full-transcript adaptive privacy and useful publication remain open. The
  reject-all publication boundary remains fail-closed.
