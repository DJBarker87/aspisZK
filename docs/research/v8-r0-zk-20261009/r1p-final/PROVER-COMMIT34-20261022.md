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

The existing serializer proofs are being assessed for reuse in Env J.
`PublicExtractedRawBridge431` is historically a separate-kernel check;
its old result is not evidence of a new Env J composition.

## Verification

Env J starts after part 33 J9052, within 9000–9199. Host jobs use individual
6G/8G/zero-swap/64-task scopes. No shipped file has changed.
