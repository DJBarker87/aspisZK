# R0 semantic soundness (premise SEM): proof job log

2026-10-08. Lead decisions Q1–Q14 as recorded in the job brief:
Q1 = positive-transfer branch; Q2 = algebraic payment relation **plus** live
append transition, runtime binding and spent-nullifier freshness, each
classified below as constrained by the proof or public-only.
Source: `crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs`
and `docs/research/v8-no-work-100-20260907/experiments/positive_transfer.rs`
at branch revision `30793447d`.

## Q2 classification (from the source, before any port)

| Property | How the source treats it | Classification |
|---|---|---|
| Nullifier derivation | Computed digest bound to `public.nullifier` at row 26·16+11 (`public_digest_lanes`) | Constrained (Part C, digest family) |
| Membership root | Computed root bound to `public.anchor` at row 56·16+11 | Constrained: the path hashes to the *stated* anchor |
| Anchor is a genuine historical root | Not referenced by the terminal | **Public-only**: on-chain program check |
| Spent-nullifier freshness | Not referenced by the terminal; only the nullifier value is public | **Public-only**: on-chain program check against the spent set; not provable by this proof |
| Recipient and change commitments | Bound to `public.recipient` / `public.change` | Constrained |
| Append: new root and carry-level frontier | `after.next_root`, `after.next_frontier[carry]` bound in-circuit; snapshot frontier levels / empty roots bound as inputs | Constrained |
| Append: pool/domain match, sequence, capacity, unchanged frontier levels | `validate_transition`: a deterministic check on public data only | **Public-only**: decidable predicate on `x`; no proof needed, but the verifier/program must run it |
| Withdrawal amount range (`1 ≤ a < 2^30`) | Host check in `composition_parts` | **Public-only**: decidable predicate on `x` |
| Runtime binding (profile/variant descriptor, statement bytes) | Absorbed into the Fiat–Shamir transcript, not a relation constraint | **Transcript binding**: enters through the FS statement `x`, not `R_pay` |

## Findings so far

1. **Q1's branch is research-only.** `positive_transfer.rs`: "Opt-in research
   design change … No production feature enables this module." Choosing it
   for R0 means R0's semantic phase is not the deployed V8 semantic phase.
2. **Slot 94 gives field non-zeroness, not integer positivity.** Its residual
   is `A₁(1014)·A₁(1015)·A₃(1014) − 1`, which forces `A₁(1014), A₁(1015) ≠ 0`
   in F_p. Integer positivity additionally needs those cells to equal the
   30-bit range-checked values (`add_value_lanes`: bits on rows 1008/1010/1012,
   reconstruction into column 10). The link is through the copy relation and
   is a Part C obligation, not given.
3. **Conservation cannot wrap.** At row 1014, `A₀ = A₁ + A₂` in F_p. If all three
   are range-checked below 2^30, then `A₁ + A₂ ≤ 2^31 − 2 = p − 1`, so the field
   equation is the integer equation. This is an arithmetic fact; it still
   depends on finding 2's copy link.
4. **Freshness and anchor validity are outside any proof of this protocol.**
   Under Q2 they become explicit public predicates enforced by the on-chain
   program. The FS/SEM theorems hold *given* them; they do not establish them.

## Finding 2 resolved (positivity) — `R0P.positivity`

The copy registry (`COPY_LINKS`, tags 1124073486–1124073489, all weight kind
0 = enabled for every variant) links `(1008,10)→(1014,0)`, `(1010,10)→(1014,1)`,
`(1012,10)→(1015,1)` and `(1014,2)→(1015,0)`. With the value-row equations,
conservation and slot 94, `R0P.positivity` proves: input = recipient + change
**as integers**, all three below 2^30, recipient ≥ 1 and change ≥ 1. It uses
only `CharP K (2^31−1)`, so it holds in QM31 with no typing premise. Its
hypotheses are exactly what the G1 row lemmas and the copy-relation equalities
must deliver; the copy equalities themselves come from the LogUp argument,
which is probabilistic (λ/χ bad sets in the SEM ledger), not deterministic.

So Q1 delivers what was intended — **conditional on** (i) G1's literal port
matching the `ValueRow`/conservation/slot-94 interfaces stated in
`Positivity.lean`, and (ii) copy-relation soundness for these four links.

## Compile record

| Target | SHA-256 | exit | wall | peak RSS KiB | swaps | axioms |
|---|---|---:|---:|---:|---:|---|
| `lean/R0P/Core.lean` | `eba6bb784803b5f00922724efc9997a8d5ab6bc55cd8c100bffd8a397dabe1f9` | 0 | 1.49 s | 3,327,872 | 0 | definitions only |
| `lean/R0P/Positivity.lean` | `0a7eaab784bc129b9995e3b7f18efde393e7d383686d1798bbe9fa7893a6ad1c` | 0 | 1.80 s | 3,327,496 | 0 | `positivity`: propext, Classical.choice, Quot.sound |
