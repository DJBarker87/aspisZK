Shared raw core and existing-codec agreement: Lean4.32, 2026-10-15

Core sourceSHA33386cb60100d583892e43cc9765e6b38fdd756a3af03950dd9688c102a78855
is fixed and imported from the separately checked shared Std-only source.
Core check exits0,10.229s, sampled group1259360KiB; agreement final exits0,
33.357s, group2918272KiB. All recorded process swaps0. Eight final theorem
axiom reports contain only subsets of propext,Classical.choice,Quot.sound.

The first agreement attempt failed on word-byte0 division-by1 and broad simp
expansion of concrete ofFn arrays. The replacement proves byte0 by div_one
and uses symbolic forall_mem_ofFn/flatMap laws; no recursion/memory cap raised.
Both exact attempted sources and receipts are retained. Failed sorryAx reports
are not accepted evidence. Final sourceSHA is in pins.json and receipt.

serialize_eq is unconditional agreement with existing PublicSourceRaw.serialize.
canonical_iff proves the coordinate/list guard equivalence. toCore/fromCore copy
fixed raw coordinates. serialize_fromCore and mapped_of_core_success connect
shared-core successful bytes to the existing PublicByteCodec encoder. The
existing Raw implementation and its dependencies are untouched. Zero withdrawal
still needs the separate nonzero/validation premise for checked decoding.

All16 recursively imported R1 source files equal the retained-cache baseline;
current source/object hashes are in cache-source-audit.json. Cached dependencies
are trusted imports, not a new full replay or binary-source attestation. Local
lake env lean used-M6000 and sampled7GiB group stop. No host/cold build occurred.

This file does not import the Lean4.31 generated serializer. Two checks of the
same shared source do not constitute a single cross-version kernel theorem.
Aeneas extraction/runtime trust and compatible-toolchain integration remain
OPEN; SourceSerializerRefines is not declared closed by this bundle.

compiler-runtime-observation.json adds the installed version and shared-library
hashes observed after the run. The small bin/lean launcher is not sufficient
to distinguish versions; these observations do not attest a reproducible build.
