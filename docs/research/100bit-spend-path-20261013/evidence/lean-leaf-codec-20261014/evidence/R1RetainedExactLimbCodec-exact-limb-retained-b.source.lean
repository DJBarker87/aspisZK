import R1RetainedFieldByteCodec
import AspisV8R15.ExactTowerBase

/-! Exact copied declaration block. The sole body replacement is its namespace/open resolution; source bytes are pinned in the adjacent manifest. -/
set_option autoImplicit false

namespace AspisR1.RetainedExactLimbCodec

open AspisR1.RetainedFieldByteCodec
open AspisV8R15.ExactTowerBase

/-! ## Literal tower coordinates -/

/-- Exact canonical-residue equivalence.  Unlike `Fintype.equivOfCardEq`,
this is the standard ring equivalence `Fin P ≃ ZMod P`. -/
def m31ResidueEquiv : M31Value ≃+* M31Exact := ZMod.finEquiv P

/-- Four canonical M31 residues in Rust field order. -/
def limbsToQM31Exact (x : QM31Limbs) : QM31Exact :=
  ⟨⟨m31ResidueEquiv (x 0), m31ResidueEquiv (x 1)⟩,
   ⟨m31ResidueEquiv (x 2), m31ResidueEquiv (x 3)⟩⟩

/-- Recover the four canonical residues in `(c0.a,c0.b,c1.a,c1.b)` order. -/
def qm31ExactToLimbs (x : QM31Exact) : QM31Limbs :=
  ![m31ResidueEquiv.symm x.re.re,
    m31ResidueEquiv.symm x.re.im,
    m31ResidueEquiv.symm x.im.re,
    m31ResidueEquiv.symm x.im.im]

@[simp] theorem qm31ExactToLimbs_limbsToQM31Exact (x : QM31Limbs) :
    qm31ExactToLimbs (limbsToQM31Exact x) = x := by
  funext j
  fin_cases j
  · simp [qm31ExactToLimbs, limbsToQM31Exact]
  · simp [qm31ExactToLimbs, limbsToQM31Exact]
  · exact congrArg x (Fin.ext rfl)
  · exact congrArg x (Fin.ext rfl)

@[simp] theorem limbsToQM31Exact_qm31ExactToLimbs (x : QM31Exact) :
    limbsToQM31Exact (qm31ExactToLimbs x) = x := by
  ext <;> simp [qm31ExactToLimbs, limbsToQM31Exact]

/-- The exact, computable four-limb equivalence. -/
def qm31ExactLimbEquiv : QM31Limbs ≃ QM31Exact where
  toFun := limbsToQM31Exact
  invFun := qm31ExactToLimbs
  left_inv := qm31ExactToLimbs_limbsToQM31Exact
  right_inv := limbsToQM31Exact_qm31ExactToLimbs

@[simp] theorem qm31ExactLimbEquiv_apply (x : QM31Limbs) :
    qm31ExactLimbEquiv x = limbsToQM31Exact x := rfl

@[simp] theorem qm31ExactLimbEquiv_symm_apply (x : QM31Exact) :
    qm31ExactLimbEquiv.symm x = qm31ExactToLimbs x := rfl

end AspisR1.RetainedExactLimbCodec
