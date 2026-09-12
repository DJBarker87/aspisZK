# Authentication prefixes retained through the later actual script

Base `8c606d9b0641892f38ad824caad0cdba8b7366ac`. New leaf only:
`lean/FSAuthenticationSuffix.lean`.

The preceding prefix result ended after C2 absorption. This leaf's
`continueRun` executes a bounded later hash script from the **actual returned
oracle** of `constructBoth`. The continuation is selected from the completed
early prefix and receives future answers only through its causal script.
The two earlier roots/cuts are not replaced by independent inputs.

`continued_prefix_answers` proves that the C1/C2 projected records are exact
takes of the **extended** final answer log and that every advertised answer
agrees with its same final full-answer cache. It derives both inclusion and
coherence; neither is a caller-supplied premise. Call repetitions, caches and
truncated-output collisions are preserved. `continue_valid` additionally covers
early failure, and `later_call_bound` proves at most q extra logged calls.

The run result distinguishes early failure (outer none) from late script abort
(outer some, inner none). Outer some is **not** complete verifier acceptance.
The main endpoint permits inner none, so an aborting later execution is not
discarded or assigned zero failure probability by definition.

## Scope and remaining producers

The later script can contain actual opening hash calls, but its concrete
generation by the selected Rust opening parser/Merkle loop is NOT proved in
this leaf. No literal Rust-to-script or old `RawHashInput`/`Digest208` grammar
conversion is claimed. This is a deterministic constructor prerequisite:
when that legal suffix exists, the old prefix answers remain synchronized with
the full later log, without needing to assume that synchronization again.

The suffix selector is one function of available early history, fixed across
continuations. It is not a collection of finished proof bodies chosen after
future challenges. Actual adversary/source-to-script coupling and its random
oracle probability law still need proof. No global soundness, adaptive ZK or
resource-normalized security result is asserted.

## Executed evidence

Focused local `lake env lean -j1 -M2048` compilation under pinned Lean 4.33.1,
commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`.
All six inherited source/artifact pairs were checked against the prior
`fs-auth-prefix-leaf-20260912/source-import-artifact.sha256` manifest. No
dependency rebuild was needed; this is a hash-validated focused leaf check,
not a fresh complete dependency/source certification.

Final command:

```
LEAN_PATH=/tmp /usr/bin/time -l lake env lean -j1 -M2048 \
  -o /tmp/FSAuthenticationSuffix.olean FSAuthenticationSuffix.lean
```

Exit 0; wall 3.08s; peak RSS 685,408,256 bytes; zero swaps. Only `propext` and
`Quot.sound` in all printed theorem axiom lists. Logs are under
`results/v8-completion-fs-extraction-20260911/fs-auth-suffix-leaf-20260912/`.
Source SHA256 `147e45d01e11e4269a0c43501b56b6f042341fbc2483220089bd5b799f07cb74`;
local artifact `990b472b8e8a31280c9c67ac2fea4ff038340401c5adf23ecef1ea405f10b3ba`.

Executable fixture: two root builders give early cut lengths 1 and 7 and eight
calls. The later script repeats input98, queries new input100, then aborts.
The final log has ten calls and seven fresh answers, later flags `[false,true]`,
with both earlier prefix lengths unchanged. This is a causal logging fixture,
not a payment or Merkle-acceptance fixture.

No old source modified, no remote job, no global replay, no commit/push by this
agent, no protocol/format/acceptance changes.
