import R1StrictWideByteCodec
import R1RetainedExactLimbCodec
import R0C.ModuloField

/-! Bridge pairs of retained canonical QM31 limbs to the existing exact wide
field representation and its eight-digit model. This is representation
plumbing only; it makes no claim about a Rust wide-field parser. -/
set_option autoImplicit false

namespace AspisR1.WideExactLimbCodec

open AspisR1.RetainedFieldByteCodec
open AspisV8R15.ExactTowerBase
open AspisWideTower

abbrev WideLimbs := AspisR1.StrictWideByteCodec.WideLimbs

def pairToExact (limbs : WideLimbs) : WideExact :=
  ⟨AspisR1.RetainedExactLimbCodec.qm31ExactLimbEquiv limbs.1,
   AspisR1.RetainedExactLimbCodec.qm31ExactLimbEquiv limbs.2⟩

def pairExactEquiv : WideLimbs ≃ WideExact :=
  (Equiv.prodCongr
    AspisR1.RetainedExactLimbCodec.qm31ExactLimbEquiv
    AspisR1.RetainedExactLimbCodec.qm31ExactLimbEquiv).trans
      (QuadraticAlgebra.equivProd wideU 0).symm

theorem pairExactEquiv_apply (limbs : WideLimbs) :
    pairExactEquiv limbs = pairToExact limbs := rfl

theorem pairExactEquiv_injective : Function.Injective pairExactEquiv :=
  pairExactEquiv.injective

@[simp] private theorem residueEquiv_natCast (x : M31Value) :
    AspisR1.RetainedExactLimbCodec.m31ResidueEquiv x =
      (x.val : M31Exact) := by
  apply ZMod.val_injective P
  change x.val = (x.val : ZMod P).val
  rw [ZMod.val_natCast_of_lt x.isLt]

private theorem retained_qm31_eq_tupleFieldEquiv (limbs : QM31Limbs) :
    AspisR1.RetainedExactLimbCodec.qm31ExactLimbEquiv limbs =
      AspisV8R19.R599CanonicalFieldTuple.tupleFieldEquiv
        (fun i : Fin 4 => ⟨(limbs i).val, by
          have h := (limbs i).isLt
          norm_num [m31Modulus, rawCandidateCount, rawWordCount,
            AspisV8R19.R445InitialBlockRejectionLaw.modulus] at h ⊢
          exact h⟩) := by
  apply QuadraticAlgebra.ext
  · apply QuadraticAlgebra.ext
    · simp [AspisR1.RetainedExactLimbCodec.qm31ExactLimbEquiv,
        AspisR1.RetainedExactLimbCodec.limbsToQM31Exact,
        residueEquiv_natCast,
        AspisV8R19.R599CanonicalFieldTuple.tupleFieldEquiv,
        AspisV8R19.R599CanonicalFieldTuple.tupleField,
        AspisV8R19.SamplerFieldDecode.decode4]
    · simp [AspisR1.RetainedExactLimbCodec.qm31ExactLimbEquiv,
        AspisR1.RetainedExactLimbCodec.limbsToQM31Exact,
        residueEquiv_natCast,
        AspisV8R19.R599CanonicalFieldTuple.tupleFieldEquiv,
        AspisV8R19.R599CanonicalFieldTuple.tupleField,
        AspisV8R19.SamplerFieldDecode.decode4]
  · apply QuadraticAlgebra.ext
    · simp [AspisR1.RetainedExactLimbCodec.qm31ExactLimbEquiv,
        AspisR1.RetainedExactLimbCodec.limbsToQM31Exact,
        residueEquiv_natCast,
        AspisV8R19.R599CanonicalFieldTuple.tupleFieldEquiv,
        AspisV8R19.R599CanonicalFieldTuple.tupleField,
        AspisV8R19.SamplerFieldDecode.decode4]
    · simp [AspisR1.RetainedExactLimbCodec.qm31ExactLimbEquiv,
        AspisR1.RetainedExactLimbCodec.limbsToQM31Exact,
        residueEquiv_natCast,
        AspisV8R19.R599CanonicalFieldTuple.tupleFieldEquiv,
        AspisV8R19.R599CanonicalFieldTuple.tupleField,
        AspisV8R19.SamplerFieldDecode.decode4]

theorem pairToExact_eq_digitsField (limbs : WideLimbs) :
    pairToExact limbs =
      R0C.ModuloField.digitsField (Fin.append limbs.1 limbs.2) := by
  rcases limbs with ⟨lo, hi⟩
  have hsplit : R0C.ModuloField.splitDigits (Fin.append lo hi) = (lo, hi) := by
    apply Prod.ext <;> funext i
    · exact Fin.append_left _ _ _
    · exact Fin.append_right _ _ _
  have hlo := retained_qm31_eq_tupleFieldEquiv lo
  have hhi := retained_qm31_eq_tupleFieldEquiv hi
  -- The eight-digit formula is the product of the two existing four-limb
  -- coordinate maps; `splitDigits` is its literal append inverse.
  unfold R0C.ModuloField.digitsField
  simp only [Equiv.trans_apply]
  rw [hsplit]
  change pairToExact (lo, hi) = _
  unfold pairToExact
  rw [hlo, hhi]
  rfl

#print axioms pairExactEquiv_apply
#print axioms pairExactEquiv_injective
#print axioms pairToExact_eq_digitsField

end AspisR1.WideExactLimbCodec
