# Address/table decoding and message binding after q22

The joint component now has a completing decoder whose inputs are the queried
address, earlier hash table, fixed public bytes, variant tag and walk bounds.
It recovers C1 and the ordinary prefix, checks the query and following-round
messages, and returns the actual completed component under the existing
trace premises. No oracle or oracle-dependent endpoint is a decoder input.

## Message checks and recovery

`IndexedMessage.read` checks the expected round label, applies the abstract
payload decoder, and requires re-encoding to reproduce the hashed payload.
Its soundness theorem exposes all three facts. Wrong labels and decoded but
noncanonical payloads are rejected. This is an abstract codec theorem; it
does not prove Rust wide-field parsing or replace the tx1/tx2 authentication
and canonicality argument.

`JointContext.parse` reads the following-round absorb frame, seeks backwards
along the selected q22 path, parses its absorb frame, and recovers the earlier
typed ordinary records. Their length determines the query and next indices.
The indexed checks bind both messages to the bytes in their absorb frames.
`JointContextSound` inverts every successful parse and proves those bindings.
The existing ordinary-prefix codec and its source obligations are unchanged.

`JointDecoder` attaches the recovered C1 and both messages to the joint
completion output. `JointDecoderTrace.decodes_after_prefix_query` proves
that this decoder succeeds and follows to the actual component. It derives
parse success, prefix recovery and the missing-answer bookkeeping from the
explicit hash chains, whole-trace reads, consistency and collision exclusions.
It does not assume a successful context parse or completed-prefix decoder.

For the inventoried 27 semantic plus four ordinary opening rows, record
length gives query index 31 and following index 32. The theorem remains a
generic component: full R1 dispatch must enforce these particular row cases.
The selected q22 path still suffices in the earlier table; its unused tail
is required only in the whole trace, as in the preceding checked theorem.

## Probability interface

The metadata attachment commutes with both trace following and the independent
answer law. `JointDecoderBound.decoded_bound` proves the adaptive continuation
bound for every completion returned by this decoder, under an explicit bound
for each fixed background-answer completion. It reuses `chainB`; it does not
assume independence of arbitrary adversarial oracle reads.

`JointRhoBound` extends the existing 21-root/modulo-sampler bound so residual
data and query interpretation may depend on the entire completed ordinary
prefix and recovered query. They cannot depend on the fresh rho answer. The
checked local bound remains below `2^-119`, with the same explicit field,
sampler-correspondence and fixed-background-function premises. This is not
the total Fiat–Shamir bound. `Qtot * maxErr` and the collision charges remain
in the eventual global theorem; no work credit is used.

## Full transcript representation

C1 is chosen by the prover and bound by the initialization hash. It must not
be moved into the fixed public statement to simplify the generic FS instance.
`TranscriptView` therefore represents it as the first message. Later messages
are payloads, and challenge values distinguish ordinary values from the q22
result, including its explicit exhaustion/error case and selected state.

The pure list lift preserves the number of ordinary rounds and adds one row
for q22. Its first message carries C1 in place of the first ordinary payload.
That replacement still requires the actual fixed row-zero byte/sampler
connection. These list identities are not that source or protocol theorem.

## Next integration obligations

The checked decoder currently returns a structured component, not yet the
generic FS protocol's complete prefix/message/challenge tuple. The next step
uses the [single R1 sampler definition](UNIFIED-SAMPLER-BRIDGE.md), which now
covers initialization, ordinary rows, the reseeded row 26, q22 at 31 and rho
at 32, with C1 as the first message. The transcript view and all completing-
decoder cases must still be shown equal to that definition, including the
fixed row-zero payload and message-type checks.

The round classifiers and full D1/D2/D3/injection/density instance remain
open. Concrete byte/public/committed-word and account/settlement correspondence,
universal mask rank and the full privacy simulator remain open. This step
changes no Rust code, runtime result or final security claim.

## Verification

Source base: `005b87b2bcf20daacf7acdc626386fc9cca9423e`.
Eleven final focused targets passed on the pinned NUC. The combined
`R1JointDecoderCheckpoint-a` passed in 1.52 seconds at 3,533,204 KiB peak RSS,
zero swap, in a 4G/6G/0 high/max/swap scope. Its 25 axiom reports contain only
`propext`, `Classical.choice`, and/or `Quot.sound`, or no axioms.

Checkpoint source SHA-256:
`85213cf362e75a38d6043899dd7dbb55c1aa2002518c7e6be5bfe2512e9b31b5`.
The [evidence bundle](evidence/lean-joint-decoder-20261014/README.md) retains
exact attempts, source snapshots, resource receipts, runner settings and
compiled objects. All fourteen central runtime fingerprints remain unchanged.
No unchanged full regression was rerun.
