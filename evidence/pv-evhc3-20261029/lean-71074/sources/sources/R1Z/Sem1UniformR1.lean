import R1Z.SamplerLawR1
import R1Z.PoleMassR1
import R1Z.GamesR1

/-! Sem1Uniform (LOG D42.3) for the concrete R1 games.  In `abR1` the attempt
coins carry every transcript read's answer as an independent uniform
coordinate; the draw is `W.dec` of the squeeze answers.  Two named premises
on the wire data, both R-wire refinement facts (LOG D45.5):

* `SemRows01 W`: `sem 1` (χ) is `s1` of the row-1 squeeze answer `sqS 1`, and
  `sem 0` (λ) does not read `sqS 1` (r1_wire.rs `begin`: λ from row 0, whose
  absorb carries C1, χ from row 1; the C1 absorb enters the address, not the
  answer, so it does not touch the coin coordinate);
* `QM31SamplerLaw s1`: `s1 b = emb (rank b mod p⁴)` with `rank` a bijection
  onto `Fin 2^256` and `emb` injective below `p⁴` (sampler.rs `qm31_sample`;
  restated from the spend path's `ExtractedQM31SamplerCorrect.sample_total`
  + `SamplerNatModel.qm31Digits_value` + `SourceSamplerByteRank.rank` =
  `ModuloField.blockRank ∘ decodeState`, an `Equiv`; the K-side carrier map
  `emb` and its injectivity are the `sampled_decode_eq_iff` content).

Result: `Sem1Uniform (drawW W) (p⁴ − 1)` for every wire satisfying them, so
`Sem1Uniform ((abR1 W N hN).draw adv x) (p⁴ − 1)` for every adversary and
statement; exact form `m·(⌊2^256/p⁴⌋+1)/2^256`.  No additive term.  ROM
address repeats do not arise here: `abR1`'s answers are independent coin
coordinates; repeats belong to the real↔middle coupling (ε_coll). -/
set_option autoImplicit false
noncomputable section
namespace R1Z.Sem1UniformR1
open R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.FsAbort R0Z.FsAbortBounds R1Z.LensR1
  R1Z.TranscriptR1 R1Z.GamesR1 R1Z.PoleMassR1 R1Z.SamplerLawR1
attribute [local instance] Classical.propDecidable

variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K]

/-- R-wire (HYP): the decoder's rows 0 and 1.  `sem 1 = s1 (row-1 answer)`;
`sem 0` does not read the row-1 answer. -/
structure SemRows01 (W : R1Wire K CommitHandle Aux) where
  s1 : OracleAnswer → K
  sem1 : ∀ (a : Fin 27 → OracleAnswer) (o : Fin 4 → OracleAnswer) (qb : Fin 8 → OracleAnswer)
    (r : OracleAnswer), (W.dec a o qb r).sem 1 = s1 (a 1)
  sem0 : ∀ (a a' : Fin 27 → OracleAnswer) (o : Fin 4 → OracleAnswer) (qb : Fin 8 → OracleAnswer)
    (r : OracleAnswer), (∀ i : Fin 27, i ≠ 1 → a i = a' i) →
      (W.dec a o qb r).sem 0 = (W.dec a' o qb r).sem 0

/-- The QM31 sampler law (restated from the spend path, HYP for the K carrier):
rank the 32 bytes bijectively into `Fin 2^256`, reduce mod `p⁴`, embed
injectively. -/
structure QM31SamplerLaw (s1 : OracleAnswer → K) where
  rank : OracleAnswer ≃ Fin (2 ^ 256)
  emb : ℕ → K
  emb_inj : ∀ x y : ℕ, x < (2 ^ 31 - 1) ^ 4 → y < (2 ^ 31 - 1) ^ 4 → emb x = emb y → x = y
  sample : ∀ b, s1 b = emb ((rank b).val % (2 ^ 31 - 1) ^ 4)

section
variable (W : R1Wire K CommitHandle Aux)

/-- The row-1 coin lens of one attempt. -/
abbrev row1Lens : Lens (R1Coins W.Cm W.Tab) OracleAnswer := coinLens W (.ans (.sqS 1))

theorem row1Lens_set (c : R1Coins W.Cm W.Tab) (u : OracleAnswer) :
    (row1Lens W).set c u = (Function.update c.1 (.sqS 1) u, c.2) := rfl

theorem row1Lens_get (c : R1Coins W.Cm W.Tab) : (row1Lens W).get c = c.1 (.sqS 1) := rfl

theorem draw_sem1 (D : SemRows01 W) (c : R1Coins W.Cm W.Tab) :
    (drawW (K := K) W c).sem 1 = D.s1 ((row1Lens W).get c) :=
  D.sem1 _ _ _ _

theorem draw_sem0_set (D : SemRows01 W) (c : R1Coins W.Cm W.Tab) (u : OracleAnswer) :
    (drawW (K := K) W ((row1Lens W).set c u)).sem 0 = (drawW (K := K) W c).sem 0 := by
  rw [row1Lens_set]
  show (W.dec (fun i => Function.update c.1 (.sqS 1) u (.sqS i))
      (fun i => Function.update c.1 (.sqS 1) u (.sqO i))
      (fun k => Function.update c.1 (.sqS 1) u (.qb k))
      (Function.update c.1 (.sqS 1) u .sqR)).sem 0 =
    (W.dec (fun i => c.1 (.sqS i)) (fun i => c.1 (.sqO i)) (fun k => c.1 (.qb k))
      (c.1 .sqR)).sem 0
  have ho : (fun i => Function.update c.1 (.sqS 1) u (.sqO i)) = (fun i => c.1 (.sqO i)) :=
    funext fun i => Function.update_of_ne (by intro h; cases h) _ _
  have hq : (fun k => Function.update c.1 (.sqS 1) u (.qb k)) = (fun k => c.1 (.qb k)) :=
    funext fun k => Function.update_of_ne (by intro h; cases h) _ _
  have hr : Function.update c.1 (.sqS 1) u .sqR = c.1 .sqR :=
    Function.update_of_ne (by intro h; cases h) _ _
  rw [ho, hq, hr]
  exact D.sem0 _ _ _ _ _ (fun i hi => Function.update_of_ne (fun h => hi (TRead.sqS.inj h)) _ _)

/-- Exact form: a `λ`-indexed family of at most `m` values is hit by `χ` with
mass at most `m · (⌊2^256/p⁴⌋ + 1) / 2^256`. -/
theorem sem1_mass_le_exact (D : SemRows01 W) (L : QM31SamplerLaw D.s1)
    (T : K → Finset K) (m : ℕ) (hT : ∀ l, (T l).card ≤ m) :
    eventMass (fun c => (drawW (K := K) W c).sem 1 ∈ T ((drawW (K := K) W c).sem 0)) ≤
      ((m * (2 ^ 256 / (2 ^ 31 - 1) ^ 4 + 1) : ℕ) : ℚ) / ((2 ^ 256 : ℕ) : ℚ) := by
  rw [R0Z.FsAbortR1.eventMass_eq_mass,
    mass_congr _ (fun c => D.s1 ((row1Lens W).get c) ∈ T ((drawW (K := K) W c).sem 0))
      (fun c => by rw [draw_sem1 W D c])]
  exact lens_sampler_mass_le (row1Lens W) (fun c => (drawW (K := K) W c).sem 0) D.s1 T m
    (2 ^ 256) ((2 ^ 31 - 1) ^ 4) L.rank m31_q_pos L.emb L.emb_inj L.sample
    (draw_sem0_set W D) hT

/-- `Sem1Uniform` for the R1 draw with `Q = p⁴ − 1`. -/
theorem sem1Uniform_drawW (D : SemRows01 W) (L : QM31SamplerLaw D.s1) :
    Sem1Uniform (drawW (K := K) W) ((2 ^ 31 - 1) ^ 4 - 1) := by
  intro T m hT
  rw [R0Z.FsAbortR1.eventMass_eq_mass,
    mass_congr _ (fun c => D.s1 ((row1Lens W).get c) ∈ T ((drawW (K := K) W c).sem 0))
      (fun c => by rw [draw_sem1 W D c])]
  exact lens_qm31_mass_le (row1Lens W) (fun c => (drawW (K := K) W c).sem 0) D.s1 T m
    L.rank L.emb L.emb_inj L.sample (draw_sem0_set W D) hT

/-- `Sem1Uniform` for the abort bridge's draw, every adversary and statement. -/
theorem sem1Uniform_abR1 (N : ℕ) (hN : 0 < N) (D : SemRows01 W) (L : QM31SamplerLaw D.s1)
    (adv : R1Adv K CommitHandle Aux) (x : Statement K CommitHandle) :
    Sem1Uniform ((abR1 W N hN).draw adv x) ((2 ^ 31 - 1) ^ 4 - 1) :=
  sem1Uniform_drawW W D L

end

#print axioms SemRows01
#print axioms QM31SamplerLaw
#print axioms row1Lens_set
#print axioms draw_sem1
#print axioms draw_sem0_set
#print axioms sem1_mass_le_exact
#print axioms sem1Uniform_drawW
#print axioms sem1Uniform_abR1
end R1Z.Sem1UniformR1
