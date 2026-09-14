# V7 current release-profile caller and snapshot source bundle

This bundle fixes the execution-profile gap in the earlier `V7CallerCurrentR18`
receipt.  That extraction used Cargo's development profile.  The current bundle
uses `--release`, matching the selected optimized runtime, and roots both the
complete observer-capable Tag-73 caller and the literal
`snapshot_query_batch_prechallenge` helper in one Charon/Aeneas graph.

## Source and generated graph

- Source revision: `e508c2b632ee02282404cd04c4c420df85455128`
- Charon: `0.1.223`
- Aeneas: pinned `d860` Linux backend
- Lean: `4.32.0`
- Cargo profile: `--release --locked --package aspis-core --lib`
- Feature: `aeneas-observer`
- Roots:
  - `aspis_core::v6_transcript::verify_v7_compact_transcript_and_relation_prepared_with_hiding_context_observe`
  - `aspis_core::v6_transcript::snapshot_query_batch_prechallenge`

Source hashes:

```text
field.rs          50f66ca87b924efe7c52a7ae274b805876d0550e16473d746d4f312e320255c3
sumcheck.rs       3f390d96a668206b9d49691cd337f58153ba70d688329697dcb73c2891dfe2dd
v6_transcript.rs  03c561a5048efc308ba4f479ebe19597a4a36dfa9b035571185372754b299fb5
LLBC              db337ead22903b7d366e3bcd652bcdeb45b19d30bd1eea775aa2427b8e269ced
Funs.raw.lean     3947059448981329b5150acba412da4860be0b4b453b367419d239e81b8704bc
Types.raw.lean    3f03fd09a9b5b878496829c0e6389f514c7a4ba4b7e138b5e315546d82f1fc52
```

Charon exited zero in 13.51 seconds at 654,996 KiB peak RSS. Aeneas exited
zero in 227.18 seconds at 3,836,232 KiB peak RSS. Both ran through Tailscale
inside a 6 GiB hard cgroup with swap disabled.

## Generated integration repairs

`Funs.raw.lean` and `Types.raw.lean` are the untouched backend outputs. The
checked generated files make source-neutral compatibility repairs for the
pinned Lean/Aeneas library: narrow umbrella imports, the already audited
mutable-iterator write-back adapter, transcript namespace qualification,
executable Boolean equality, one curried fold, the no-op diagnostic callback's
literal result shape, and explicit/correctly typed wrapping-shift operands.
No Aspis function body is replaced by a model or external axiom.

The complete generated graph kernel-imported successfully. Peak RSS for its
largest target (`Funs`) was 3,199,024 KiB with zero swap.

## Proved scope

The files in `proof-r20/` prove the actual generated release-profile field,
half, multilinear, tensor, deferred grouped-binary, component, accumulator,
256-term dot, and snapshot functions. The strongest current results are:

- `generated_live_six_component_accumulator_corresponds`
- `generated_prequery_dot_256_corresponds`
- `generated_snapshot_prechallenge_corresponds`

Every printed axiom set is contained in
`[propext, Classical.choice, Quot.sound]`; there is no `sorryAx` or
project-specific axiom.

This closes the release-profile generated computation layer, not all of G1/G2.
The remaining immediate source obligation is to derive the literal six-component
accumulator and its canonical/length premises from the translated successful
`finish_onefold_relation` path, then identify the snapshot fields with the
maintained restored K1.3 checkpoint.
