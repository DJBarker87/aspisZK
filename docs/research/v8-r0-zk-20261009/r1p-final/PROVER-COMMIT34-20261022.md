# Prover commitment continuation 34

Branch: codex/cx-prover-commit34-20261022. Actual base: 0583e6bd5 (D146);
requested research pin: 26b922be6. Work in progress; target not yet established.

## Scope statement

D146 restricts the statement domain to images of shipped `r0::Public` values
whose `public_bytes` returns `Ok`. This restricts statements, not adversaries
or oracle queries. D143 observables are public statement bytes, proof bytes,
and answers to adversary queries. Timing and other side channels are outside
the privacy contract. No endpoint premise has yet been removed.

Announced quantifier before:
```lean
∀ x : R0Z.FsStatement.Statement K CommitHandle, ...
```
Announced quantifier after (scope statement; pending construction):
```lean
∀ x : {x : R0Z.FsStatement.Statement K CommitHandle // DeployedStatement x.1}, ...
```
These are the domain quantifiers only; the complete endpoint before/after is
recorded when its specialization is implemented. The existing endpoint is
unchanged at this checkpoint.

## Stage 1: serializer and domain

The existing serializer dependency cone is now recompiled in Env J (J9053–
J9060), using the existing pinned generated definitions with import paths
ported. Computational definitions are unchanged. `serializer-source-pins.json`
compares `public_bytes`, `private_public`, and `withdrawal_public` verbatim
against extraction source revision 781929374. This is reuse of historical
extracted code, not a new owned-reference extraction contrary to D144.

`ProverCommitDomain34` (J9066) fixes a field-preserving source image into
`R0P.Public WideExact`, including exact source live u64 index and both
frontiers. `DeployedStatement` quantifies over the **actual extracted Public**
carrier and successful extracted `public_bytes`, not a handwritten admission
predicate. `lower_image` proves a canonical source projection has a left
inverse. `source_bytes_exact` proves every successful representative returns
one fixed model byte function, without choosing a source from the output.
`public_bytes_ok` proves existence of a representative returning exactly
`ok (.Ok (sourcePubBytes x))` on the announced domain. The source success
result also proves all serialized raw words canonical. No withdrawal-nonzero
restriction or truncation is introduced. `sourcePubBytes` has its vector
bound proved symbolically (at most 1455 bytes).

`outside_no_serializer_success` proves that a source representative outside
the domain cannot return any successful public serialization. This is not yet
a theorem about the full retry/proof-producing caller: that caller can first
return an entropy error, and Aeneas failure/divergence must not be silently
renamed `Error::Semantic`. No new API accepting arbitrary wide records has
been invented. The source-to-runtime boundary remains P6; this is one-kernel
composition of extracted definitions, not a new claim of Rust semantics.

## Verification

Env J starts after part 33 J9052, within 9000–9199. Host jobs use individual
6G/8G/zero-swap/64-task scopes. No shipped file has changed.


Stage 1 checkpoint: J9061–9062 and J9064–9065 are rejected proof drafts;
J9063 accepts the intermediate domain, superseded by J9066's exact source
vector result. Accepted axioms are subsets of [propext, Classical.choice,
Quot.sound]. Full source snapshots and raw receipts are in
`evidence/prover-commit34-20261022/lean`. No shared existing module/object was
replaced: ported serializer modules use new module paths. The historical
namespaces retaining `431` are composed here under Lean 4.32, not by mixing
kernel objects.
