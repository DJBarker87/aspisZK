# D473 ActualInput source binding review

The inherited full Link and restore definitions remain byte-identical. This
review does not treat an equality about a newly constructed model input as an
association with the deployed call. No native function is defined to return
the wanted model answer.

The accepted previous Builder.successful_canonical is conditional on its
explicit Except-valued build. The new work targets two concrete gaps in that
model's representation:

* PointArray represents the ten initialized stack entries with an actual
  fixed-size Aeneas array. Every index is Fin10, every direct store changes
  the array's value view exactly by List.set, and the fold commutes with the
  old point-store model. This excludes the silently ignored out-of-range
  store permitted by an unrestricted List index.
* QueryStores constructs the preceding challenge, current sample and ascending
  Boolean-suffix writes at the source counters, including round9's empty
  suffix. Final stores are ten challenges, without a round10 sample. These
  are normalized query histories. A proof that they equal the full successive
  source history (rather than merely give canonical arrays) is still needed.
* BuilderShape proves the successful build's actual output length vector is
  exactly29 copies of1024. It preserves the existing early base/d/g rejection,
  setup/helper/balance/finish failures, and the ordered26 lifts/h1/g/d output.
* The uncredited SampleCarrier draft and unsubmitted PassShape draft target the exact U64 dividend/quotient/remainder
  casts and all quotient-word stores. They do not prove the full native
  array-iterator source association merely by proving word bounds.

## Source edges that still prevent installed credit

`state_only_candidate_prefix.rs:788–804`: the actual nested any/chain checks,
16-byte stack write and decoder Option must be related to acceptedBase and
acceptedExtensions over the same array/List views. InputBytes.read_write is
available but does not alone bind those calls, slice ranges or short-circuits.

`:805–838`: setup and finish are opaque value-projection continuations. They
may be instantiated by their actual call fragments for a value-only invariant,
but their full error maps and unchanged input/output associations must be
recorded. The actual helper is the PF registry/helper at :980–991 and
pair_forest_semantic_oracle.rs:171–179, with the CopyImbalance-to-Public map.
HelperResult preserves its pole errors; matching that pure execution to the
actual selected fixed-array traversal and inverse operation remains necessary.

`:839–844`: the ordered array::from_fn, map/copied/collect and three to_vec
carriers must share the successful helper and checked d/g values. The new
length theorem proves model shape; it does not discharge this association.

`r0_transcript.rs:126–155`: native high-word-first iter_mut writes each quotient
back to the same word, executes all8 passes, then selects digits0–3. The model
uses a high-word-first List view, and the uncredited word-equation draft identifies wrapping and
cast obligations. No discarded restoration is permitted. Native
comparisons of exact returned samples are finite validation, not proof of
all write-back continuations or a generation receipt.

`state_only_hiding.rs:1593–1627`: every direct point store must identify the
same initialized ten-entry array; prove the completed-round and nested-loop
invariant for all successful prefixes and early oracle errors. New bounded
indices close local bounds, not this full execution relation. Complete native
schedules, including terminal callback and first-stop errors, are supporting
finite validation only.

ActualInput therefore remains OPEN unless these concrete source associations
are supplied. Under own-1, V370/D381/D386 covers source-to-machine-code, not
these missing source-to-model relations. Rust/Aeneas/Charon agreement is
reclassification within existing tool trust; no T field or endpoint premise
is introduced.

OwnedPublicPlan remains next: op222 selected Slice/array carriers, exact sparse
initialized tuple bytes, Vec ownership transfer, IntoIter/drop/error/abort and
same-execution global first-stop resource trace. Transcript879/890 remain
deferred, including the terminal callback, until those preceding links hold.
