import R0P.SemDeg

/-! G25: selected claim-dependent mask, ported from R0Z.MaskedProtocol.
Source pin d2b7413259a75100db9d1c722d88932bfea28fb9.
C = crates/aspis-core/src/state_only_hiding.rs. Definitions factorExponent
through maskValue are copied byte-for-byte, with their source citations.
Tower coefficients use R0P.PackBasis, as in the soundness terminal. -/
set_option autoImplicit false
noncomputable section
namespace R0P.Mask
open R0P R0P.SemSource R0P.SemDegree R0P.SemBadSets Polynomial
variable {K : Type} [Field K] {F : Subfield K}

/-- C:392-393, [0,2,4,6,8,10,12,14,16,18,20,22,24,26,13,25]. -/
def factorExponent (c : Fin 16) : Fin 27 :=
  ⟨if c.val < 14 then 2 * c.val else if c.val = 14 then 13 else 25,
    by split_ifs <;> omega⟩

/-- C:394-395, [1,3,5,7,9,11,15,17,19,21]. -/
def maskOnlyFactorExponent (c : Fin 10) : Fin 27 :=
  ⟨if c.val < 6 then 2 * c.val + 1 else 2 * c.val + 3,
    by split_ifs <;> omega⟩

/-- C:446-465,535-552: multiplication by (1,i,u,iu), column modulo four. -/
def towerBasis (B : PackBasis F) (j : Fin 4) : K :=
  if j.val = 0 then 1 else if j.val = 1 then B.i else if j.val = 2 then B.u else B.i * B.u

def mulTowerBasis (B : PackBasis F) (v : K) (j : Fin 4) : K := towerBasis B j * v

/-- C:484-492. Family 0 gives 3*S0+22*S1; family 16 gives
275*S0+150*S1, the selected evaluator's two forms (C:494-512). -/
def maskLinear (family : Nat) (α : Fin 10 → K) : K :=
  ∑ j : Fin 10, ((3 + 22 * j.val + family * (17 + 8 * j.val) : Nat) : K) * α j

structure MaskFactors (K : Type) where
  c1 : Fin 16 → K
  maskOnly : Fin 10 → K
  explicitG : K

/-- C:561-580. Exponentiation is the mathematical power table, not a
kernel evaluation of the Rust repeated-multiply/addition-chain algorithms. -/
def maskFactors (B : PackBasis F) (α : Fin 10 → K) : MaskFactors K where
  c1 c := mulTowerBasis B (maskLinear 0 α ^ (factorExponent c).val)
    ⟨c.val % 4, Nat.mod_lt _ (by omega)⟩
  maskOnly c := mulTowerBasis B (maskLinear 0 α ^ (maskOnlyFactorExponent c).val)
    ⟨c.val % 4, Nat.mod_lt _ (by omega)⟩
  explicitG := 1 + maskLinear 16 α ^ 26

/-- C:612-643,647-674: the selected mask, including all ten mask-only
columns. The latter source implementation evaluates the same coefficients
by Horner's rule. D (lane 28) has zero factor and is absent here. -/
def maskValue (B : PackBasis F) (c1 : Fin 16 → K) (maskOnly : Fin 10 → K)
    (g : K) (α : Fin 10 → K) : K :=
  (∑ c, (maskFactors B α).c1 c * c1 c) +
    (maskFactors B α).explicitG * g +
    ∑ c, (maskFactors B α).maskOnly c * maskOnly c

/-- Degree 27 after substituting the committed trace MLEs, rather than
only checking the degree-26 factors with the column values held constant.
All row sums remain behind the existing symbolic MLE degree theorem. -/
theorem maskValue_vdeg (B : PackBasis F) (t : Trace K) :
    VDeg 10 (fun _ => 27) (fun α => maskValue B
      (fun c => honestClaims t α 0 (Fin.castLE (by omega) c))
      (fun c => honestClaims t α 0 ⟨16 + c.val, by omega⟩)
      (honestClaims t α 0 27) α) := by
  classical
  have hlinear (family : Nat) : VDeg 10 (fun _ => 1) (maskLinear (K := K) family) := by
    apply vdeg_sum Finset.univ
    intro j _
    apply vdeg_smul
    apply vdeg_mono (vdeg_proj j)
    intro i
    simp only [Pi.single_apply]
    split_ifs <;> omega
  have hfactor (e : Fin 27) (j : Fin 4) : VDeg 10 (fun _ => 26)
      (fun α => mulTowerBasis B (maskLinear 0 α ^ e.val) j) := by
    apply vdeg_mono (vdeg_smul _ (vdeg_pow (hlinear 0) e.val))
    intro i
    have := e.isLt
    omega
  have hg : VDeg 10 (fun _ => 26) (fun α : Fin 10 → K => 1 + maskLinear 16 α ^ 26) := by
    simpa only [Nat.mul_one, Nat.zero_max] using
      vdeg_add (vdeg_const 10 (fun _ => 0) (1 : K)) (vdeg_pow (hlinear 16) 26)
  unfold maskValue
  apply vdeg_add (d := fun _ => 27) (e := fun _ => 27)
  · apply vdeg_add (d := fun _ => 27) (e := fun _ => 27)
    · apply vdeg_sum Finset.univ
      intro c _
      exact vdeg_mul (hfactor (factorExponent c) _) (vdeg_honestClaims_zero t _)
    · exact vdeg_mul hg (vdeg_honestClaims_zero t 27)
  · apply vdeg_sum Finset.univ
    intro c _
    exact vdeg_mul (hfactor (maskOnlyFactorExponent c) _) (vdeg_honestClaims_zero t _)


#print axioms factorExponent
#print axioms maskOnlyFactorExponent
#print axioms towerBasis
#print axioms mulTowerBasis
#print axioms maskLinear
#print axioms maskFactors
#print axioms maskValue
#print axioms maskValue_vdeg
end R0P.Mask
