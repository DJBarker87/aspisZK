# Semantic terminal and opening-claim inventory

Inspection basis: `/Users/dominic/ZK/.worktrees/100bit-spend-path`, HEAD `0dbaf0c8d576a8da71e031b89cef2c9083c67cca`. This is a source-only inventory. No Lean process was run and no proof source was edited. File paths and SHA-256 values for the inspected declarations are in `SEMANTIC-TERMINAL-INVENTORY.sources.json`.

## The source statement and candidate relation

The source terminal uses a row-space trace `t : Fin 29 → Fin 1024 → K`. `R0P.SemView.coeffsOf π t` converts it to coefficient-space messages by `fun c j => t c (π.symm j)`; `rowsOf π m` converts coefficient messages back by `fun c r => m c (π r)`. `dot_coeffWeight_coeffsOf` states exactly

```lean
AspisR0.RoundNormalization.dot
  (AspisR0.Opening.coeffWeight π w) (coeffsOf π t c) =
AspisR0.RoundNormalization.dot w (t c)
```

The opening statement constructed by `R0P.SemSource.openingStmt` contains:

- `W := c2Words x h g`, where the C2 words replace lanes 26 and 27 of the typed context; `base` is supplied by `c2Words_base` and the C2 base premise.
- `points := openingPoints α`, `pointClaims := y`, `inactive := copyInactiveRows`, and `transport := x.transport`.
- `extraWeight := libraWeight α`, `extraClaims := x.extraClaims`.

The point order is literal: `openingPoints α 0 = toR0 α`; index 1 is `toR0 (successorPoint α)`; index 2 is `toR0 (xor12Point α)`. `toR0 p b = p ⟨9 - b.val, ...⟩`; `xor12Point` toggles coordinates 7 and 6. The semantic candidate's three point claims are

```lean
honestClaims t v j l := dot (eqWeight (openingPoints v j)) (t l)
```

and the witness statement expresses the same claims after coefficient transport:

```lean
∀ j l,
  pointClaims j l = dot (coeffWeight transport (eqWeight (points j))) (candidate l)
```

The R0FS candidate relation is `R0FS.Witness q t`:

```lean
 t ∈ Lambda q.W ∧
 (∀ j l, q.pointClaims j l =
   dot (coeffWeight q.transport (eqWeight (q.points j))) (t l)) ∧
 (∀ l, q.extraClaims l = dot q.extraWeight (t l)) ∧
 (∀ l i, exactInitialEncoder (t l) i ∈ Sfield l)
```

Thus candidate membership, all three transported point claims, all per-lane extra claims, and encoder-coordinate subfield typing are conjuncts of this relation. `opening_decision_witness` obtains an `R0FS.Witness`; `accepted_no_hit_extracted` then sets the row trace to `rowsOf transport mcoeff`. Its local `hy` proof uses `dot_coeffWeight_coeffsOf` to identify the parsed `pointClaims` with `honestClaims`. Its local `hyx` identifies the statement's `extraClaims` with `honestExtra`.

`R0P.SemD3Glue.witness_baseTyped` consumes the final witness conjunct. Its conclusion is `BaseTyped x.F t`, namely `∀ c, c.val < 26 → ∀ b, t c b ∈ x.F`. It uses `x.lanesF` to identify each of lanes 0–25's `Sfield c` with `x.F` and applies the statement transport. The R0 typed context separately carries per-lane base typing for committed words, a distinguished subfield `F`, public-base typing, and C2 word base typing.

## Terminal-to-semantic conclusions

`R0P.SemD3.d3_core` is the candidate-level terminal bridge. Its inputs include the prime-characteristic equation `P = 2^31 - 1`, typed context `x`, a `PackBasis x.F`, candidate trace `t`, and `hA : BaseTyped x.F t`. It also requires three named G14 properties for that `x,t`: `HonestRows`, `VirtualDeg`, and `ChecksAccept`; an actual 24-challenge vector `r`, sumcheck polynomials, the exact `sumcheckChecks` premise at `honestClaims t (semSlice r 14 10)`, and `∀ i : Fin 24, ¬ candidateRoundBad ... i`. Its conclusion is

```lean
ProductionHolds x.pub (r 0) (r 1) t ∧ CopyLinkBalance x.pub t
```

`HonestRows` is the Boolean terminal equation: `virtualPoly ... (ofBool b)` equals the Boolean equality weight `eqwB 10 (preZc pre) b` times `lanesComp` plus the `μ * H1` term and the `μ² * inactive-H1` term. The inactive term is literally

```lean
(1 - copyActiveLiteral (copySelectors (rowSel (rowOf b)))) * t 26 (rowOf b)
```

and the source statement's `inactive` field is `copyInactiveRows = Finset.univ.filter (fun b => ¬ CopyActiveRow b)`. The witness relation has no separate inactive-sum conjunct; the inactive expression appears in the terminal and is handled by the sumcheck/LogUp path.

`ProductionHolds` is the conjunction of `Holds` for value, occupancy, asset, schedule, path, digest, Poseidon-scalar, and the copy family at the two challenges. `CopyLinkBalance` says that every copy link in `copyLinks` with nonzero `copyLinkWeight` has equal producer and consumer tuples.

`R0P.Semantic_sound_closed` consumes the same semantic shape through explicit inputs: `BaseTyped`, `PublicBase`, a `PackBasis`, `¬ BadLogUp`, a Boolean terminal equation, `IndDeg 27 10`, accepted claim-zero sumcheck, and exclusions `¬ BadAlpha`, `¬ BadMu`, `¬ BadZc`, and `¬ BadTheta`. It concludes `ProductionHolds ∧ CopyLinkBalance`. `semantic_extraction_closed` has these premises and concludes `InputNoteExtracted`; the file also has `extraction_step` as the stated production/copy-to-payment extraction implication. `semantic_positivity` is separate and additionally requires `Holds positiveFamily` to conclude bounded natural transfer values and positivity.

The final spend relation used by the source is `R0P.InputNoteExtracted pub A`:

```lean
∃ sk salt : Fin 8 → K, ∃ path : Fin 24 → Bool × Digest K,
  pub.nullifier = nullifierHash sk salt ∧
  pub.anchor = merkleRoot
    (noteCommitment (ownerKey sk) (A 10 1008) pub.assetId salt) path
```

The `SourceData` interface explicitly assigns `paymentWitness := fun x t => InputNoteExtracted x.pub t`. Its comment says its operations are data parameters without proof fields; `R0P.SemSource` supplies the concrete model definitions referenced by the later bridge.

## Parsed-prefix theorems and premises

`R0P.SemD3Glue.opening_decision_witness` has literal inputs `Q : FS.Prefix (R0FS.Stmt K Sfield) ...`, opening message `om`, `hdec : R0FS.decision Q om = true`, `hcard : SemSource.cardOK Q = true`, `hno : ¬ R0FS.good Q.statement Q.rounds`, and `hfirst` saying the first parsed `(values y, field γ)` opening challenge has `γ ≠ 0`. Its conclusion is `∃ t, R0FS.Witness Q.statement t`.

`R0P.SemD3Glue.accepted_no_hit_extracted` adds the three universal G14 assumptions (`hrows`, `hdeg`, `hchk`), a parsed semantic prefix `P`, `hdec : SemSource.decision B P m = true`, no hit in `sourceDataWithFallback`, and the first-opening nonzero premise. Its conclusion is `∃ t : Trace K, InputNoteExtracted P.statement.pub t`. The proof unpacks the accepted decision and q22 card guard, gets the opening witness, transports the coefficient tuple to row space, rewrites its point/extra claims as `honestClaims`/`honestExtra`, uses no-hit to exclude the round bad events, and applies `d3_core`.

The unmasked outer `R0P.SemD3Glue.d3` is a 31-round `FS2.D3` theorem. Its explicit protocol-level premises include characteristic 2³¹−1, a `PackBasis`, duplex parameters `p`, message and decoder functions, a round budget, and `hσ26 : ∀ s, p.σ 26 s = .opening (R0C.V3.DQ.σQ 0 s)`. It states D3 for `combinedProtocol` and `duplexRows`, with `combinedDecision` as verifier.

The masked path has a parallel candidate-level theorem, `R0P.Mask.accepted_no_hit_extractedZ`. Its inputs are characteristic 2³¹−1; a fallback point; an arbitrary `maskClaims` function plus `hMask : MaskDegree maskClaims`; a `PackBasis`; a masked prefix `P`; `hdec : decisionZ maskClaims B P m = true`; no hit in `sourceDataWithFallbackZ`; and the same kind of first opening challenge nonzero premise. It concludes `∃ t, InputNoteExtracted P.statement.pub t`.

`R0P.Mask.d3Z` is the 32-round masked `FS2.D3` theorem. In addition to characteristic 2³¹−1, `maskClaims`, `hMask`, `PackBasis`, duplex parameters, message, decoder, and round budget, it requires `hσ27 : ∀ s, p.σ 27 s = .opening (R0C.V3.DQ.σQ 0 s)`. The statement is D3 for `combinedProtocolZ` and `duplexRowsZ`, verified by `combinedDecisionZ`. The proof uses the source extractor's failure/no-hit pair to apply `accepted_no_hit_extractedZ`.

The masked terminal is not the unmasked terminal by itself. `terminalZ` is `maskClaims y0 yx α + η * terminalValue ...`; `virtualPolyZ` substitutes honest point claims, `honestExtra`, and `α` into `maskClaims`, then adds `η * virtualPoly`. `MaskDegree` requires `VDeg 10 (fun _ => 27)` for that mask term for every transport permutation and trace. `sumcheckChecksZ` accepts a `claim` at the first sumcheck boundary, while the unmasked `sumcheckChecks` has first boundary zero. `maskTotal` is the Boolean sum of the mask term; `originalTotal` is the Boolean sum of the original terminal. `originalTotal_zero_of_masked_accept` requires `hMask`, accepted masked sumcheck, `¬ badAlpha`, and `¬ etaBad claim (maskTotal ...) (originalTotal ...) eta` to conclude `originalTotal = 0`. The no-hit lemmas supply the eta/alpha/early-round exclusions used before `semantic_of_total_zero`.

`MaskProtocol.maskClaimsR0` has the literal body

```lean
maskValue B
  (fun c => y0 (Fin.castLE ... c))
  (fun c => y0 ⟨16 + c.val, ...⟩)
  (y0 27) alpha + yx 28
```

and `MaskValue.maskValue` sums the selected `c1`, explicit-G, and ten mask-only factors. The final `+ yx 28` is the lane-28 Libra claim. `honestExtra π t α l` is `dot (libraWeight α) (coeffsOf π t l)`, where `libraWeight α j` is `α 8 ^ j.val` for indices below 28, `α 9 ^ (j.val - 28)` for indices 28–55, and zero otherwise.

The masked schedule has semantic message/challenge positions 0–24, with the `maskSum` claim at index 14 before η, α at 15–24, circle rows at 25–26, and five opening rows at 27–31. The masked opening view uses point challenges at `cs[15 + j.val]`. The unmasked parser takes 24 semantic rounds, then two circles, and its point challenges are at `cs[14 + j.val]`; its first opening challenge is at round 26. These are the literal source offsets.

## Current R1 raw-opening/binding shapes

`AspisR1.ConcreteBinding.binding` takes `W`, a final word `V`, six linear functionals `F`, a base functional `F0`, six claim vectors `Y`, base claim `c0`, challenges `gamma/kappa/alpha0/alpha1`, two degree-six polynomials, and an auxiliary message `f`. It requires `gamma ≠ 0`, membership exclusions from `gammaBad`, `kappaBad`, `firstBad`, and `secondBad`; a matching set `M` of at least 9558 positions; both fold/encoder equalities on every `i ∈ M`; the final pairing equation; and two boundary equations. Its conclusion is one `t ∈ candidates W` satisfying all six equations `F j (t l) = Y j l` and `F0 (exactInitialMessageCurve t gamma) = c0`.

`MatchingSupport.Data` gives those six functionals/claims literally as `F : Fin 6 → Functional E`, `Y : Fin 6 → Fin 29 → E`, with `F0`, `c0`, `gamma`, `kappa`, and round-pairing data. `MatchingSupport.Claims` is the existential tuple and those same six-plus-one functional equations. `RawOpening.rawClaims` replaces `F`/`F0` by arbitrary raw rows `raw : Fin 7 → Fin 1024 → K`, with row 0 used for the base batch claim and rows `j+1` used for the six `Y` claim families. `large_matching_implies_raw_claims` additionally takes the `Good`, `AcceptedPairing`, and 9558-cardinality premises for the data after `withRows iota raw`.

`D18RawPoint.pointRowMap_eq_row_sum` is a separate generic identity: for arbitrary `p : Fin 10 → K`, arbitrary coefficient message `m`, and a ring hom `iota`, it identifies `rowMap iota (tensorPoint p) m` with `∑ r, m (row r) * iota (booleanRow p r)`. `tensorPoint_eq_booleanRow` says `tensorPoint p j = booleanRow p (row j)`. The `raw` matrix in `RawOpening` remains an arbitrary seven-row input; these declarations do not name a semantic opening point, an R0 transport, or a relationship between a particular raw row and one of the three source `openingPoints`.

For literal field and relation comparison: R0's `R0FS.Witness` includes `∀ l i, exactInitialEncoder (t l) i ∈ Sfield l`; R1's `ConcreteBinding.candidates` is a `Lambda W` membership and its binding conclusion has no `Sfield` or `BaseTyped` field. R0 has three point-claim families and the separate per-lane Libra `extraClaims`; R1's current raw conclusion has six raw `Y` families plus one base-batch claim. R0's inactive set/terminal factor is explicit in the R0 statement/terminal; no separate inactive-set or inactive-sum premise appears in the listed R1 raw claim/binding signatures. These are statement shapes only; this inventory does not assert a mapping between them or whether any R1 premise supplies an R0 premise.
