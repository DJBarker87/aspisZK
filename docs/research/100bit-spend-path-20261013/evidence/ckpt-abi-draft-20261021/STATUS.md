# Checkpoint ABI draft

Base: 73772c55b, codex/cx-ckpt-abi-draft-20261021. No merge or push.

## Stage 1: source inspection

The physical source is `crates/aspis-r1-cost-probe/src/verifier.rs:326–435`.
`checkpoint` writes the fields in C5 order. `resume` checks length/header,
then proof hash, public hash and checksum with short circuit, before decoding.
It rejects repeated queries. The saved-ten domain has header next=10; the
source accepts other next values up to 22, so this is not a whole-resume
all-input specialization.

`OraclePortCheckpointOracleC5.resumer` always issues all three digest calls;
it cannot be used as a total source refinement on rejection paths.
`OraclePortCheckpointPreparedC5.decode` allows duplicate queries; its roundtrip
alone is not a source resume theorem. `R9PoolCheckpointCodec` explicitly uses
an unrelated logical encoding, not the physical ABI. Existing extracted
`resume_three_inputs`/`successful_resume_calls` expose source digest witnesses,
not writer/decoder equality. R22's retained remaining-summary explicitly leaves
the full owned-Vec loop, allocation/iterator joins and cursor sequencing open.

`OraclePortFrozenOrder.dV_frozen` contains admission, parsing, queries,
six slots and arithmetic, with no checkpoint stage. The checkpoint joins at
the surrounding verifier driver. No concrete frozen caller/tree identity is
available here to instantiate `ConeJoin .checkpointAbi`.

Planned additive work: a source-shaped reference for the saved-ten ABI with
short-circuit digest failures and query uniqueness; total model codec facts,
accepted save/resume state and exact ordered reads; explicit source witness
boundary. This is not an assertion that the extracted codec is identified.
