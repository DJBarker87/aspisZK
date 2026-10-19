import R0Z.K4Values
import R1Z.RfOwnLimb

/-! D49.4 C2: RF-round with its coordinates (zf1/DESIGN-P-CERT.txt §2.3 RF-round).

`RfChain.rf_round_of_coords` reduced `rf_round` (with `ιr = RfChain.iotaR`) to
`z4c (roundMaskMap (src t)) = unflat (col Rnd t)`.  Here that identity is
proved for the column matrix `Rnd i t = flat (z4c (roundMaskMap (src t))) i`
(the Z4c coordinates of the source's round image, four tower limbs each), for
any source family: every round coefficient of a mask tape lies in `K₄` when
every α does (`roundMaskMap_mem`), so `unflat ∘ flat` is the identity on its
coordinates.  The closed form of these columns for the checker's sources is
the Rust `round_row` / `tail_row` (probe.rs:262-337, 2256-2278); matching the
extracted Rust builders to `z4c ∘ roundMaskMap` is C3 (and the Lean closed form
of `round_row` itself is not proved here). -/

set_option autoImplicit false

noncomputable section

namespace R1Z.RfRound

open scoped BigOperators
open R0P R0P.SemSource R0Z.MaskLayout R0Z.HonestView R0Z.Partition R0Z.D12 R0Z.K4
open R1Z.RfChain

attribute [local instance] Classical.propDecidable

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

variable (B : PackBasis F) (hB : PackField B)

theorem pureTrace_mem (m : M K F) (c : Fin 29) (s : Fin 1024) : pureTrace B m c s ∈ K4 B hB := by
  by_cases h0 : c.val < 16 ∨ c.val = 26
  · rw [pureTrace_fixed B m c h0]
    exact (K4 B hB).zero_mem
  · by_cases h1 : c.val < 26
    · have hc : c = ⟨16 + (c.val - 16), by omega⟩ := Fin.ext (by simp only; omega)
      rw [hc]
      exact F_le_K4 B hB (R1Z.RfOwnLimb.pureTrace_maskOnly_mem B m ⟨c.val - 16, by omega⟩ s)
    · have hc : c = ⟨27 + (c.val - 27), by omega⟩ := Fin.ext (by simp only; omega)
      rw [hc]
      exact R1Z.RfOwnLimb.pureTrace_ext_mem B hB m ⟨c.val - 27, by omega⟩ s

theorem maskLinear0_mem {a : Fin 10 → K} (ha : ∀ i, a i ∈ K4 B hB) (fam : ℕ) :
    R0P.Mask.maskLinear fam a ∈ K4 B hB :=
  sum_mem (fun j _ => (K4 B hB).mul_mem (natCast_mem _ _) (ha j))

theorem maskFactors_mem {a : Fin 10 → K} (ha : ∀ i, a i ∈ K4 B hB) :
    (∀ c, (R0P.Mask.maskFactors B a).c1 c ∈ K4 B hB) ∧
      (∀ c, (R0P.Mask.maskFactors B a).maskOnly c ∈ K4 B hB) ∧
      (R0P.Mask.maskFactors B a).explicitG ∈ K4 B hB := by
  refine ⟨fun c => ?_, fun c => ?_, ?_⟩
  · exact (K4 B hB).mul_mem (towerBasis_mem_K4 B hB _)
      ((K4 B hB).pow_mem (maskLinear0_mem B hB ha 0) _)
  · exact (K4 B hB).mul_mem (towerBasis_mem_K4 B hB _)
      ((K4 B hB).pow_mem (maskLinear0_mem B hB ha 0) _)
  · exact (K4 B hB).add_mem (K4 B hB).one_mem ((K4 B hB).pow_mem (maskLinear0_mem B hB ha 16) _)

theorem payloadMaskLinear_mem (π : Fin 1024 ≃ Fin 1024) {a : Fin 10 → K}
    (ha : ∀ i, a i ∈ K4 B hB) (t : Trace K) (ht : ∀ c r, t c r ∈ K4 B hB) :
    R0Z.PayloadSplit.maskLinear π B a t ∈ K4 B hB := by
  obtain ⟨hc1, hmo, hg⟩ := maskFactors_mem B hB ha
  have hy : ∀ j c, honestClaims t a j c ∈ K4 B hB :=
    fun j c => R0Z.K4Values.honestClaims_mem _ t ht a ha j c
  rw [R0Z.PayloadSplit.maskLinear_apply]
  refine (K4 B hB).add_mem ?_ ?_
  · unfold R0P.Mask.maskValue
    exact (K4 B hB).add_mem ((K4 B hB).add_mem
      (sum_mem (fun c _ => (K4 B hB).mul_mem (hc1 c) (hy _ _)))
      ((K4 B hB).mul_mem hg (hy _ _)))
      (sum_mem (fun c _ => (K4 B hB).mul_mem (hmo c) (hy _ _)))
  · rw [← extraLinear_apply, R1Z.RfOwn.extraLinear_sum]
    exact sum_mem (fun i _ => (K4 B hB).mul_mem
      (R1Z.RfObs.libraWeight_mem _ ha i) (ht _ _))

variable {Bat : Type} [BatchedLayer K Bat]

/-- Every round coefficient of a mask tape lies in `K₄` (under `SemK4`). -/
theorem roundMaskMap_mem (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K)
    (hsem : ∀ i, ch.sem i ∈ K4 B hB) (m : M K F) (j : Fin 10) (i : Fin 28) :
    R0Z.Z4Maps.roundMaskMap (Bat := Bat) π B ch m j i ∈ K4 B hB := by
  rw [roundMaskMap_apply, R0Z.PureRounds.A_pure, R0Z.PayloadSplit.L_round,
    R0Z.PayloadSplit.rounds_apply]
  refine R0Z.K4Values.interpolate_coeff_mem _ _ (fun k => sum_mem fun tail _ => ?_) i.val
  exact payloadMaskLinear_mem B hB π (R0Z.K4Values.roundPoint_mem _ ch hsem j k.val tail)
    _ (pureTrace_mem B hB m)

/-- **RF-round.**  The `rf_round` premise with `ιr = iotaR` and
`Rnd i t = flat (z4c (roundMaskMap (src t))) i`, for any source family. -/
theorem rf_round (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K)
    (hsem : ∀ i, ch.sem i ∈ K4 B hB) {N : ℕ} (src : Fin N → M K F) :
    ∀ t, R0Z.Z4Maps.roundMaskMap (Bat := Bat) π B ch (src t) =
      iotaR B (alpha ch) (R1Z.CertSound.col
        (fun i t' => flat B hB (z4c (R0Z.Z4Maps.roundMaskMap (Bat := Bat) π B ch (src t'))) i) t) :=
  rf_round_of_coords π B ch src _ (fun t =>
    (unflat_flat B hB _ (z4c_mem B hB (fun j i => roundMaskMap_mem B hB π ch hsem (src t) j i))).symm)

#print axioms pureTrace_mem
#print axioms maskFactors_mem
#print axioms payloadMaskLinear_mem
#print axioms roundMaskMap_mem
#print axioms rf_round

end R1Z.RfRound

end
