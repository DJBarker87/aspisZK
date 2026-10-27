# Whole-run callback obligation

The proved outer equation has this shape:

```
client = op233 S2 S2 >>= fun equal =>
  if !equal then semantic_error
  else runCPS adaptedEntropy public compiled S2 hash 8 store state 0
```

`runCPS` composes the exact retry branches with
`op226 public >>= Continue035.continueAfter ...` at every attempt.
Neither this Result equality nor the named suffix equations is yet an
operational trace refinement. A callback-invocation semantics and its
connection to every retained suffix are missing. A static dependency set,
a dictionary-output congruence, or an equality after erasing a trace cannot
supply that connection.

The next theorem must quantify over whole-run execution prefixes, including
prefixes ending in rejection, failure or divergence. For each fixture shape,
its conclusion must constrain every dictionary invocation to an explicit
finite set, with the native-association boundary typed exactly. Then derive
one exclusion for every dictionary entry outside that set. No callback set
or exclusion is claimed from the current source equations alone.
