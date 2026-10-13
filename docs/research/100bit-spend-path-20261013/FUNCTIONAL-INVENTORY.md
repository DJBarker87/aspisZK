# R1 functional source inventory

Read-only shape comparison for the current R1 cost probe. This identifies
candidate existing definitions only. It does not establish source-semantic
correspondence, prove a gate, or assert that the probe's D18 coordinate map is
the map used by the R0 formal statement. Source hashes are in
`FUNCTIONAL-INVENTORY.sources.json`.

## Candidate declarations

The closest existing source-level model is the generic R0 opening statement in
`R0P.SemSource`:

- `SemView.lean:113–131` defines `succCarry`, `successorPoint`, `xor12Point`,
  `toR0`, and `openingPoints`. `openingPoints α` has three points: the input,
  its polynomial binary successor, and the point toggling the source
  coordinates 7 and 6. `toR0` reverses ten coordinates because these source
  points are MSB-first while `eqWeight` is indexed by little-endian row bits.
- `SemD3.lean:28–30` defines `honestClaims t v j l` as
  `dot (eqWeight (openingPoints v j)) (t l)`.
- `R0.OpeningDefinitions.lean:33–41` defines Boolean `eqWeight` and
  coefficient reindexing `coeffWeight π w j = w (π.symm j)`. The actual
  discrepancy at `OpeningDefinitions.lean:76–79` is the point claim minus
  `dot (coeffWeight D.transport (eqWeight (D.points j)))` with the row message.
  Thus the three multilinear functionals have reusable mathematical shapes,
  including a transport parameter, but the R1 `tau` embedding into this
  parameter is not defined in these declarations.
- `SemView.lean:64–67` defines the Libra coefficient functional as
  `alpha[8]^j` for indices `j < 28`, `alpha[9]^(j-28)` for `28 ≤ j < 56`,
  and zero otherwise. `openingStmt` installs `libraWeight α` and
  `x.transport` together at lines 188–194. `MaskValue.lean:97–124`
  independently states and proves the corresponding `libraTail` dot-product
  split into the same two 28-coefficient blocks.
- `Copy.lean:239–245` defines `CopyActiveRow` and `copyInactiveRows` as the
  complement of the literal active-row mask. `LaneMap.lean:944–958`
  (`lane_inactive_sum`) identifies the Boolean-cube inactive helper sum with
  `∑ r ∈ copyInactiveRows, t 26 r`; its comment explicitly says it identifies
  the sum but does not assert it vanishes.

For the two circle-point functionals, the closest reusable algebraic pieces
are `R0.ChordImage.domainX/domainY` (`ChordImage.lean:21–24`) and
`Wide.FinalEncoder.exactFinalLinear_apply` (`FinalEncoder.lean:66–72`), which
evaluates the natural final coefficients at a stored log-18 line point.
`Wide.FinalEncoder.exactInitialEncoder_eq_circleLift` (`FinalEncoder.lean:125–185`)
states the radix-four lift from that final line evaluator to the exact initial
encoder at stored circle coordinates. In the active R1 worktree,
`lean/NaturalProjection.lean:108–144` provides the generic radix-four
natural-basis functional identity with weights
`[1, x, T2(x), x*T2(x)]`, where `T2(x)=2x²-1`, and shifts the next-stage
argument to `T4(x)`. These are candidate reusable pieces for the circle
functionals; no inspected R0 declaration names the exact two R1 `SecureCirclePoint`
row-weight vectors as a pair of functionals.

## Probe shape and correspondence gaps

`weights.rs:73–85` obtains the three points from
`aspis_core::state_only_prefix::r0::statement_points` and pairs them with the
two provided circle points. `weights.rs:91–100` forms point row weights,
inactive indicators, the two-block Libra powers, and the tensor weights.
For S1/S2 point rows, each row is obtained by `Variant::row(j)` and its ten-bit
equality weight uses `points[k][9-b]`. `transport.rs:4–14` defines
`TAU = [3,4,2,0,1]` and maps the five base-four digits of `j` to digit slots
`TAU[d]`. This is a coefficient-index-to-row function. In the Lean opening
API, `TypedContext.transport` is an equivalence from row indices to
coefficient indices and `coeffWeight` applies `π.symm` (see
`OpeningDefinitions.lean:29–41`). Therefore the candidate orientation is that
Rust `Variant::row` corresponds to `π.symm`; it should not be substituted
directly for `π` without an explicit inverse/orientation check.

The generic R0 declaration permits an arbitrary transport equivalence and does
not name the R1 D18 permutation or its five-digit `tau`. The R0 on-chain D13
transport is separately defined by `r0/transport.rs`; it is not the R1 S1/S2
digit map. The only `TAU` declaration found in the scanned source is the Rust
probe `transport.rs`; no corresponding Lean D18 `tau=[3,4,2,0,1]` declaration
was found in the inspected R0P/R0 sources.

There is also a coordinate-order obligation. Rust `statement_points` emits
`[alpha, successor, absorption]` in source array order; `successor` walks
coordinates 9 down to 0, and absorption flips 7 and 6. Lean explicitly applies
`toR0` to all three points before constructing row `eqWeight`. The probe's
`raw` function indexes each stored point at `9-b`. This is a plausible
MSB-source/LSB-row correspondence, but this inventory did not prove the point
arrays and Lean `openingPoints` are identical under the D18 bit-pair transport.

For the R1 Libra contraction, `twofold_libra_weights` (`weights.rs:41–57`)
combines the first two radix-four fold digits. It uses the flattened position
`16*j+s`, selects block `index/28`, and exponent `index%28`, retaining only
positions below 56. This resembles `SemView.libraWeight`'s two 28-term blocks,
but equivalence still depends on the exact row/coefficient indexing and the
normalization/order of the low-digit fold weights.

For each circle point, the probe initializes the first radix-four factor to
`[1,y,x,x*y]`; subsequent factors use `[1,x,T2(x),x*T2(x)]` and repeatedly
double the node (`weights.rs:79–84`, `double` at line 9). This has the same
local radix-four factor pattern as the generic natural-basis identities noted
above. The complete equality between these two row-weight vectors and the
formal R0 circle evaluator is not established by the inspected declarations.

The inactive functional is selected on the transported row index in Rust:
`opening::inactive(self.variant.row(j))`. Its shape corresponds to the R0
literal `copyInactiveRows` indicator only after the transport map is aligned.
The optimized grouped contraction also forms 16-slot masks after the first
two folds (`grouped_inactive_pair`, `weights.rs:12–39`); that grouping is an
implementation of the selected indicator pairing, not a separately identified
Lean declaration.

The names above are candidate reuse points for root review. No source was
changed and no theorem, transport equivalence, or security conclusion is
claimed here.
