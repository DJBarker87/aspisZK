# Recovering and completing the prefix across the opening-domain transition

The decoder can now recover an ordinary opening prefix together with all
preceding semantic records, starting from the table before the next absorb.
The initialization and domain-transition queries remain explicit. This
extends [the initializer bridge](INITIAL-EDGE-BRIDGE.md); it is not the
complete R1 Fiat–Shamir instance.

## Recovery from the earlier table

`DuplexRecordAnchor` extends the existing record-order result to a later
anchor address: once the last ordinary advance precedes that anchor, every
earlier absorb and advance, and the initializer, precedes it too. The proof
reuses the old no-collision first-read lemma and the previous ordinary-prefix
ordering result. It does not assume the desired table lookups succeed.

`ReseedPrefix` first recovers and strictly parses the P3 domain/tag frame,
then runs the initializer-based walk on its predecessor state. `CarryLast`
replaces only the last semantic record's next state by the reseed output.
The preceding state, absorbed state, label and payload remain unchanged,
as does record count. This implements the established model in which row
26's challenge value is unchanged but its carried state includes the domain
hash. It does not insert a new challenge row or change any Rust operation.

`OpeningWalk` handles subsequent ordinary records until that strict reseed
decoder succeeds. `ReseedSeparation` proves that it cannot stop early on an
ordinary advance: the advance address is 33 bytes and the reseed frame is
62. `OpeningWalkCells` derives the unique predecessor lookups and those
non-stopping facts from actual consistent table cells.

`OpeningPrefixTrace.walk_before_next` composes the two parts. Its premises
are whole-trace consistency, the first-read bound, the old duplex and added
parsed-state collision complements, the explicit two chains and their read
facts, and the next address's endpoint prefix. It derives the complete
earlier table contents and the successful base recovery. Its conclusion is
the actual C1 root followed by the carried semantic records and ordinary
opening records, in order. Neither table-cell presence nor a successful
base-decoder result is left as a premise of this trace theorem.

For the inventoried schedule, the structural pattern is 27 semantic rows
followed by four ordinary opening rows, ending before the q22 row. The
theorem also permits zero ordinary opening rows, so it includes the boundary
before gamma. Instantiating the concrete message codec and source execution
remains necessary; the pattern alone is not that refinement.

## Indexed message decoding and challenge completion

`RawRoundDecode` checks the recovered label against the expected round index
and uses the abstract `Params.dec` for the payload. Its successful constructor
round trip relies on the existing `Params.decEnc` law. The append and offset
lemmas connect both record segments without resetting the opening round
index. These results do not supply a concrete Rust codec or prove that every
byte string accepted by an arbitrary `Params.dec` is canonical.

`OpeningPrefixCompletion` applies that decoder to the recovered raw records.
It then reuses the old `completeRounds`: every challenge uses its own absorbed
state's squeeze cell; only the last semantic carried state changes to the
reseed output. The explicit completed-round theorem checks both the message
order and challenge indices across that boundary.

`PrefixAnswers` lists exactly the absent squeeze cells of the typed prefix,
deduplicates them, and applies the existing positional `DQ.accFrom` lookup.
With a coherent table, supplying the actual oracle answers on that computed
missing list yields the actual completed rounds. It does not require all
earlier squeeze answers to have been queried before the next absorb.

`PrefixNextLaw` reuses the existing background-mean split and ordinary duplex
sampler law. It averages the missing prefix answers outside the next round's
two fresh answers. Its bound retains the explicit requirement that every
fixed prefix completion satisfies the supplied per-round bound. This is an
independent-answer identity; proving freshness, disjointness and trace
following for the complete prefix is still necessary before using it as an
adaptive source-execution bound.

## Remaining composition

The next connection must combine these records and pending squeeze cells
with the existing q22 selected-prefix recovery and rho component. It must
also preserve pending semantic answers through the reseeded row and handle
the next ordinary sampler's trace following. The complete completing decoder,
generic injection/density and D1/D2/D3 instance remain open.

The runtime has not changed. Rust/public/committed-word correspondence,
account and settlement guards, the actual-field privacy simulator and the
final private-spend claim remain separate obligations. The generic
`Qtot * maxErr` factor and charged collision terms are retained, with no
work-normalization credit.

## Verification

Source base: `beee9c934d2dd43ed9fe708c88036c1add2f541c`.
Fifteen final focused targets passed. `R1OpeningPrefixCheckpoint-a` imports
the preceding initializer checkpoint and the new recovery/completion modules.
It passed in 1.38 seconds at 3,530,180 KiB peak RSS with zero swap, in a
4G/6G/0 high/max/swap scope. Its 38 axiom reports contain only `propext`,
`Classical.choice`, and/or `Quot.sound`.

Checkpoint source SHA-256:
`42a2501e9e823d025f0b6ef7c265576f79987dd50ca735c23710ea612043fdfe`.
The [focused evidence bundle](evidence/lean-opening-prefix-20261014/README.md)
retains exact sources, failed attempts, capped NUC receipts, runner settings
and compiled objects. No unchanged runtime regression or historical full
manifest was rerun.
