# Next connection: trace following for query completion

The independent-answer [completion law](QUERY-COMPLETION-LAW.md) is checked.
The next obligation is to connect its sampler to the actual consistent
oracle trace, using the older background-read framework.

## Existing interface

`R0C.V3.Dec` in
`docs/research/v8-r0-close-20261007/lean/R0C/V3/Gen.lean` returns a triple:
an own-read sampler, pending background cells, and a function that produces
the prefix, message and current challenge. `Inj3.decodes` requires this
decoder to follow the actual trace suffix to that exact output.

The existing `R0C.V3.bfollow_ok` in `BSOk.lean` supplies the mechanical
trace-following result, given:

1. A consistent suffix trace.
2. No duplicate addresses across pending cells and the own-read events.
3. Every such address is absent from the starting table and read in the suffix.
4. Every own `ask` precedes all subsequent own events. A spawned squeeze
   need not precede the following advance read.

Its conclusion gives the output function the actual oracle answers:
`fill H pending ++ (runOut H own).2.map H`. The checked
`QueryDecoder.fromAnswers_correct` and `QueryNextLaw.output_append` are
designed to identify that output. The bound then uses the existing
background law and generic first-read framework, after their remaining
instance premises are discharged.

## Root's intended focused route

First prove the following-round component, before integrating all earlier
rounds. Use the concrete absorb endpoint following q22, the table before
its first read, and `QueryNextLaw.own`. Keep whole-trace consistency,
collision complement, query-chain reads, and new-round reads explicit.
Do not assume all eight query advances are in the preceding table.

- Use the checked first-read seek result to characterize every `missing`
  address as a squeeze on the selected predecessor path, absent from that
  table. Whole-execution squeeze reads supply its read premise.
- Reuse `tableBefore_eq`, `before_total` and `read_traceFrom` to put those
  missing cells in the suffix. They may be read before or after the new
  squeeze; imposing an order between them would be unjustified.
- Derive distinctness from the old collision complement and encoding
  separation. In particular, selected-prefix states must differ from the
  following absorb's output. A bare list-dedup fact is insufficient to
  exclude overlap with that following round's squeeze.
- Derive absorb-before-new-squeeze/advance from `noColl_prefix_after` and
  their literal leading state bytes. Reuse the suffix-order lemmas for
  `OrderOK` and the freshness conditions of `bfollow_ok`.
- Apply `bfollow_ok`, then the checked actual-answer and output-splitting
  equalities. This closes only the local component's trace-following
  result; full `Inj3` still needs the full R1 prefix and decoder.

The old worked construction is
`docs/research/v8-r0-sem-proof-20261008/lean/R0P/MaskDuplexDecodes.lean`,
especially `combinedDecodes` and its `hnd`, `hfresh`, `hord`, `hfill` and
output-equality steps. Its earlier records describe single-step rounds and
must not be used unchanged for the q22 predecessor of rho.

Useful generic names include `noColl_injective`, `noColl_prefix_after`,
`squeezeA_injective`, `squeezeA_ne_advanceA'`, `squeezeA_ne_absorbA`,
`advanceA_ne_absorbA`, `before_ne`, `tableBefore_self`, and `traceFrom_eq`.

No proof in this note is claimed complete. The initial/public hash edge,
opening-domain transition, earlier messages and R1 D1/D2/D3 remain the
larger instance obligations.
