# R512 rewrapped-hashcons projection translation receipt

This is a failed translation receipt, not a proof result.

R512 built the complete original R500 hash-cons definition map before pruning,
then reserialized only original `Deduplicated` and `HashConsedValue` wrapper
locations as fresh unique inline `HashConsedValue` definitions. The preflight
resolved the original map without missing IDs or cycles, emitted no final
`Deduplicated` references, and independently decoded the projected output.
That decoded JSON equals the authorized R510 fully expanded projection,
including retained Fun1/Fun32/Fun33, all types, globals, and traits.

The one authorized fresh translation imported the rewrapped input successfully,
then exited 2 after 0.18 s, peak RSS 57,728 KiB, zero swap. It reached the
actual retained Fun32 panic-formatting raw-pointer operation and stopped at:

```
Unsupported operation: &raw const (*msg) with_metadata(copy msg.metadata)
core/src/fmt/mod.rs:815:4-823:5
  generated from core/src/str/mod.rs:575:8-575:12
```

No generated Lean was accepted, compiled, or proved. This is a serialization
and translation boundary result only; it introduces no library semantics or
axioms.
