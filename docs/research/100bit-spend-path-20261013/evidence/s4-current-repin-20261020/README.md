# S4 current `four_dots` source/extraction checkpoint

This packet repins `crates/aspis-r1-cost-probe/src/fast_dots.rs::four_dots`
from revision `f2c084bc8f51c02f4c58b6d0a4e3dd450867e1f5`. The exact source
file SHA-256 is `32d90c30e36dea620da0619bfdd9bd7fce3973fb22a3d8c30deb42a79a0ccd61`;
the function occupies bytes `[678,2292)` (SHA-256
`4c4407dbebaa2726c998b32245275357a23517a3941098103f92ab3a69a537cd`),
lines 13–47. `source_checker.py` confirms the snapshot and 13 range/reduction
critical source shapes; this check is textual, not a semantic proof.

## Emission and generated-body handling

Charon emitted the pinned body to LLBC (hash
`e14403e8af1bcae616983467eaab7706dac93a9319728974d595645b0f3648a4`). The
current combined Aeneas binary failed on this LLBC at
`InterpBorrows.ml:2731` (exit 2, 0.603 s, 89,584 KiB process RSS, 72,667,136 B
cgroup peak, swap 0); this diagnostic is retained under
`aeneas-current-failure/`.

The unmodified Aeneas r18 binary from the pinned r18 tool workspace processed
the *same LLBC* successfully. Its complete generated `Funs.lean` retains the
outer four-slot function, seven-by-four base loops, eight-limb accumulation,
reduction loop, tail parsing and final add. It exited 0 in 1.605 s (123,024
KiB process RSS, 116,150,272 B cgroup peak, swap 0; 2 GiB high / 4 GiB max /
swap 0). The LLBC and raw output hashes are in
`alternate-aeneas-v1/receipt.json`; raw generated Lean sources are in the
candidate directory. The Aeneas executable SHA-256 is
`959659a6aafc6a6a975b4dc67ee9d779a269b988bd44b3b31a77cf023b1709e3`.

The selected proof owner is `FunsOpsV4.lean`, a mechanically checked adapter
over all 19 generated declarations. It removes the generated resource-option
commands and template import, replaces the 11 external operation references
with fields of an explicit `FourDotsOps` parameter, and threads that parameter
through the generated call graph. The reversible checker normalizes the
adapter back to the entire raw generated `Funs.lean`, modulo only those listed
changes. It therefore checks the whole loop-body text and call/operand order;
the eleven operation implementations remain explicit parameters and are not
proved by this owner. The adapter compiled with Lean 4.32.0 under a 1 GiB
high / 2 GiB max / swap 0 scope (exit 0, 1.606 s, 2,401,828 KiB process RSS,
307,830,784 B cgroup peak). Its `#print axioms` results for the public
`four_dots` and the inner eight-limb loop contain only
`[propext, Classical.choice, Quot.sound]`.

`Types.lean` aliases the generated field/EbyK nominal types to the exact
existing `EbyKPushExplicitTypesV1` source-shaped owner and retains the
generated closure array shapes. It compiled under Lean 4.32.0 with exit 0,
1.104 s, 2,364,132 KiB process RSS, 282,419,200 B cgroup peak, swap 0. This
is a type/layout adaptation; the alias itself does not prove the external
operations. The imported `EbyKPushExplicitTypesV1` source SHA-256 is
`23594328c5bf0746f7bb3b036904f70d15b3e561a08aa51426c7920fe8e5b0ee`; its
selected object SHA-256 is
`5ad5824261d7d2eff4898e8d61eb403c401f2cbe3300e3d30ddc08078e34e36d`.

## Mathematical connection and remaining boundary

The exact source uses base offsets `120*slot + 4*term + byte` with
`slot < 4`, `term < 26`, `byte < 4`; the retained
`R22ControlBounds.fast_dot_offsets` theorem gives `< 480`. Tail offsets are
`480 + 32*slot + 16*term + byte` with `slot < 4`, `term < 2`, `byte < 16`;
`fast_dot_tails` gives `< 608`. The Rust source snapshot/checker verifies the
offset expressions and the fixed `q[..608]` conversion; these arithmetic
lemmas do not by themselves prove iterator bounds or operation behavior.

`FastDotFoldedBatches.actual_reducer_after_seven` proves that a list of at
most seven batches, each containing at most four products bounded by
`(2^31-2)^2`, can be passed through the retained reducer with the expected
modular sum. It does not yet instantiate those products from the emitted
eight-limb callback. The caller's actual `WideExact`, byte parsing, M31/QM31,
array construction, EbyKDot, and reducer behavior remain the explicit
`FourDotsOps` boundary. Hence this checkpoint is a current-source extraction
and loop-body repin, plus explicit mathematical range/reducer references; it
does not close the complete S4 Rust-to-arithmetic proof.

The two existing mathematical owners are `lean/R22ControlBounds.lean` (SHA-256
`c77a94f6c87d9d8c00d13445a189214006865962f57fedb878382c620c968bad`, receipt
`evidence/overflow-freedom-20261019/receipts/R22ControlBounds-20261020T074902.621577Z/command.json`)
and `lean/FastDotFoldedBatches.lean` (SHA-256
`48f286dea37123aed19dce5bfb317e35d8be7dce6bc2ef3d4cc8f7149cee550a`, receipt
`evidence/overflow-freedom-20261019/receipts/FastDotFoldedBatches-20261020T073723.933670Z/command.json`). Their relevant `#print axioms` outputs are in the corresponding `out.log` files and contain only standard Lean axioms.

See `manifest.json` for hashes of the selected source, generated candidate,
and receipts. Superseded stale-Fmt Funs compilation evidence is not selected;
the accepted Funs receipt is from the `s4-current-funs-ops-v4fmt` attempt and
uses the repaired Aeneas/Fmt overlay pinned in its preflight.
