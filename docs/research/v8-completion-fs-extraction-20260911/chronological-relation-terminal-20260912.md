# Chronological relation terminal — 2026-09-12

`lean/SameBodyChronologicalRelationTerminal.lean` composes the constructed
authenticated scalar package with a same-body `Ready` relation observation.
It isolates the minimum remaining source producer as four objects fixed by the
ordinary/image relation implementation: early fields, the causal pre-tau
strategy, ordinary scalar and terminal weight. Its only equality premise is
that the canonical parsed word is the realised word produced by that causal
strategy; it assumes neither consumer nor terminal success.

`consume_is_some` proves the actual `SameBodyRelation.consume` succeeds from
that causal-word equality, using the exact authenticated opening increment
carried by `Ready`. `run_terminal` then executes the independent terminal
Boolean and returns either explicit terminal rejection or a certificate
containing:

- the chronological authenticated-scalar alternative;
- derived `consume.isSome = true`; and
- the executed terminal success.

`TerminalCertificate.accepted_on_produced` transports terminal success to the
literal final premise of the already checked generic
`produced_check_constructs_terminal_zero`. Thus the terminal-zero alternative
requires no additional mathematical premise; it is deliberately left as the
existing generic theorem rather than re-normalising its large concrete QM31
conclusion in this leaf.

Still open are construction of OOD `Data` and `SourceRelationProducer` from
the pinned source/Rust execution, payment acceptance/extraction, literal Rust
refinement and FS probability coupling. The historical
`SameBodyOpenedTerminal.lean` was not imported: its current source replay hit
recursion-depth failures, so no failed artifact or `sorryAx` entered this
endpoint.

## Focused evidence

- Base revision: `66400a885c8426897200d74aa396b15385717086`
- Lean 4.32.0, commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`
- `MemoryHigh=8G`, `MemoryMax=9G`, `MemorySwapMax=0`, `-j1 -M8192`
- Exit: 0
- Wall time: 4.94 seconds
- Peak RSS: 6,762,952 KiB
- Swap: 0
- Source SHA-256:
  `11709663dd18b4279df648880eb5034a3b418e0cc39ed8d18053a161054e7c04`
- Olean SHA-256:
  `36fd2040acaa36f6276cf0e0143d569a1eb38df44e02bd289a1ba9093cadbc6f`
- Axioms: `propext`, `Classical.choice`, `Quot.sound`
