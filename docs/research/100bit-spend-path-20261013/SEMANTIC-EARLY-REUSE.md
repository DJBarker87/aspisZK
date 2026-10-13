# Early semantic-round reuse inventory

This is a read-only source inventory of the existing masked-semantic path. It records theorem interfaces and the maps visible in source; it does not assess premise provenance, probability accounting, or whether any security obligation is closed.

Pinned worktree revision: `5731808b200ee9784b2ed018b9cb9cd7e51be5a2` (`/Users/dominic/ZK/.worktrees/100bit-spend-path`). No Lean build was run for this note.

## Interfaces and route

`R0P.Mask.early_candidate_to_prefixZ` is in [`MaskEarly.lean`](../v8-r0-sem-proof-20261008/lean/R0P/MaskEarly.lean#L16). Its hypotheses include a parsed 25-row masked prefix (`hlen : rs.length = 25`, `hparse : semChalsZ rs = some cs`), parsed C2 words (`hc2 : c2OfZ rs = some (hw,gw)`), a trace `t` in `LambdaRows x.transport (c2Words x hw gw)`, a selected row `i : Fin 24` with `i.val < 14`, a semantic current message, and `candidateRoundBad x.pub B t (fun _ => 0) ... i`. Its conclusion is `semanticBadZ ... ⟨x, rs.take i.val⟩ sm ...`.

The proof first converts masked rows with `baseRoundsZ` and messages with `unmaskSem`. It constructs the prefix candidate in one of two ways:

- For `i.val < 2`, `candidate_mem_before_c2N` supplies `padC2Trace t` as a candidate of the truncated prefix. The proof then applies `semRoundBad_pad_early` to transfer the round-0/1 bad event between `t` and `padC2Trace t`.
- For `2 ≤ i.val`, `candidate_mem_after_c2N` supplies `t` as a candidate using the C2 words already parsed from the prefix. `semRoundBad_strat_early` changes the strategy argument for rounds below 14.

The shared continuation `hfinish` packages candidate membership and the corresponding semantic round badness into `semanticBadZ` for the truncated prefix. `no_hit_early` ([`MaskEarly.lean`](../v8-r0-sem-proof-20261008/lean/R0P/MaskEarly.lean#L69)) adds `semSlotZ` to identify the current masked message/challenge pair, then calls `no_hit_roundZ` with the supplied `hno : ¬ hitFrom ... (rs ++ tail)`. Thus the source implication has explicit parse, C2, LambdaRows, and no-hit hypotheses; this note makes no claim about how those hypotheses are obtained.

## Candidate and padding maps

The candidate set is defined by `R0P.SemSource.candidates` in [`SemD2.lean`](../v8-r0-sem-proof-20261008/lean/R0P/SemD2.lean#L38). Its branch on `rounds.length < 2` is

```lean
(LambdaRows x.transport (c2Words x padWord padWord)).filter
  (fun t => t 26 = 0 ∧ t 27 = 0)
```

At length two, the `.h1 h g` branch uses `LambdaRows ... (c2Words x h g)`; for longer prefixes it uses the words returned by `c2Of`, or the empty set when parsing fails. `padWord` is `exactInitialEncoder (fun _ => 0)` and `c2Words` updates lanes 26 and 27 with the supplied words ([`SemView.lean`](../v8-r0-sem-proof-20261008/lean/R0P/SemView.lean#L147)). `padC2Trace t` updates those same two trace lanes to zero ([`SemView.lean`](../v8-r0-sem-proof-20261008/lean/R0P/SemView.lean#L54)). `SemPad.lean` proves `padWord = 0` and `padC2Trace t l = t l` for `l ≠ 26,27` ([`SemPad.lean`](../v8-r0-sem-proof-20261008/lean/R0P/SemPad.lean#L26)).

`mem_Lambda_pad` ([`SemPad.lean`](../v8-r0-sem-proof-20261008/lean/R0P/SemPad.lean#L208), theorem at lines 246–251) has the interface

```lean
(x : TypedContext K Sfield) (h g : InitialWord K) (t : Trace K)
(ht : t ∈ LambdaRows x.transport (c2Words x h g)) :
padC2Trace t ∈ LambdaRows x.transport (c2Words x padWord padWord)
```

Its proof rewrites `LambdaRows` to coefficient form, preserves each prior agreement position by inclusion into the padded agreement set, handles lanes 26/27 using the zero-codeword facts, and uses equality of the other lanes. `candidate_mem_before_c2N` ([`MaskPrefix.lean`](../v8-r0-sem-proof-20261008/lean/R0P/MaskPrefix.lean#L37)) then proves that this padded trace belongs to `candidates x (rs.take i.val) sm` for `i.val < 2`, including the zero conditions at lanes 26 and 27. `candidate_mem_after_c2N` ([`MaskPrefix.lean`](../v8-r0-sem-proof-20261008/lean/R0P/MaskPrefix.lean#L15)) instead uses the parsed C2 words and truncated-prefix `c2Of` equality for `i.val ≥ 2`.

The round-event transport lemmas are in [`SemD3Glue.lean`](../v8-r0-sem-proof-20261008/lean/R0P/SemD3Glue.lean#L638): `semRoundBad_pad_early` states equivalence of the padded/unpadded `semRoundBad` at `i.val < 2`, and `semRoundBad_strat_early` states equivalence for two strategy functions at `i.val < 14`. The former reduces the cases to `lambdaRoundBad_pad` / `chiRoundBad_pad` from `SemPad.lean`; the latter unfolds the classifier and simplifies its early branches.

## Early event indices

`candidateRoundBad` in [`SemD3.lean`](../v8-r0-sem-proof-20261008/lean/R0P/SemD3.lean#L64) is `semRoundBad` with the virtual polynomial strategy and fixed polynomial list. `semRoundBad` in [`SemRounds.lean`](../v8-r0-sem-proof-20261008/lean/R0P/SemRounds.lean#L772) selects these cases by challenge index: lambda at 0, chi at 1, theta at 2, ten `zcRound` checks at indices 3 through 12, and `BadMu` at 13; later indices are alpha rounds.

`earlyRounds_cover` in [`MaskEarly.lean`](../v8-r0-sem-proof-20261008/lean/R0P/MaskEarly.lean#L217) takes as its sole event-side premise

```lean
∀ i, i.val < 14 → ¬ candidateRoundBad pub B t (fun _ => 0) r i
```

and concludes the conjunction of `¬ BadLogUp pub t (r 0) (r 1)`, `¬ BadTheta ... (r 2)`, `¬ BadZc ... (semSlice r 3 10)`, and `¬ BadMu ... (r 13)`. Its proof relates LogUp to the lambda/chi rounds, theta to round 2, the ZC aggregate to its ten per-round events, and mu to round 13. The theorem is a conditional correspondence from absence of those fourteen candidate-round events to the named predicates.

`no_hit_early` supplies the source-level route to that absence: for each `i < 14`, it obtains a slot with `semSlotZ`, applies `early_candidate_to_prefixZ`, and derives a contradiction with `no_hit_roundZ`. This describes the implication chain in the files; it does not add an assertion that the underlying no-hit premise holds.

## Eta row and later schedule boundary

`MaskD2.etaBad` is `S ≠ 0 ∧ claim = M + eta*S` ([`MaskD2.lean`](../v8-r0-sem-proof-20261008/lean/R0P/MaskD2.lean#L17)). The same file separately defines `etaSomeBad` as an existential union over a finite candidate set and proves a cardinality bound by the candidate-set size (`etaSomeBad_card`, lines 85–101). The documented semantic challenge sampler bound is for `semChal` over `State`, with denominator `P^4` (`etaBad_semChal_mass`, lines 65–72); the candidate-union wrapper is `etaCandidates_semChal_mass`, lines 132–145. These definitions place the eta event at index 14, after the first fourteen event indices. `combinedD2BudgetZ` documents the later piecewise schedule at lines 147–155. No inference is made here about the sampler law or whether this bound is applicable to another route.

## Source hashes

SHA-256 values below are for the exact worktree files at the pinned revision above.

| Source | SHA-256 |
|---|---|
| `R0P/MaskEarly.lean` | `d059910517c04de436fcaa20d0c67bcc4e59ae80715a71ac6ce25f7a892c98b7` |
| `R0P/SemPad.lean` | `b5cd6f82b930644a81bbeabdfc4003425e52ddf5eefdc0c9485698d9e82de164` |
| `R0P/MaskD2.lean` | `22af138da175023e657cd78ca98c15468b7c29ca166d5d14e3d02abb687e1041` |
| `R0P/SemView.lean` | `a8e8fab6e0efaa76bf64f1197edb5ab51327f8906aecdb668c55885e94837fbd` |
| `R0P/MaskPrefix.lean` | `4bbf715dd3c5cf4b1b8976ec81c3c657402369caab15b2f99fbc8fe3a40f52f5` |
| `R0P/SemD3Glue.lean` | `60830349937666ec050499c10bdb51e5c17811a949edd494f9205f0ee45ad852` |
| `R0P/SemD2.lean` | `2b68437dfd6ba62cd023013a5b514987255550124c0eca4abb03a26a560397c0` |
| `R0P/SemD3.lean` | `68cd2542aff4f20ead2f5855663cf3e743817725f2714cc3400a21b0f651c74b` |
| `R0P/SemRounds.lean` | `564b9026233a36736f524407f357b44e173173139e52b9c4c6effbd88335bfd4` |
| `R0P/MaskView.lean` | `f27198834fa43256002cce83de7eeef675fecd88e89db0ee7a2bc00ef3a8b44b` |
| `R0P/MaskBadSets.lean` | `18b0499811001773be7ec5d2ff2e9463a2ff22048281595b76008033427862f7` |
