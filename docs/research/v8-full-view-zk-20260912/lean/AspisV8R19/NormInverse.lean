import AspisV8R19.InverseChain
import AspisV8R19.SamplerCirclePolicy

/-! Source-shaped norm/conjugate inversion using the proved base addition
chain. Exact field algebra; word-level CM31/QM31 execution remains separate. -/
set_option autoImplicit false
namespace AspisV8R19.NormInverse
open AspisV8R15.ExactTowerBase
noncomputable section

def baseInverse (x : M31Exact) : M31Exact :=
  InverseChain.decode (InverseChain.wordChain ⟨x.val,ZMod.val_lt x⟩)

theorem base_inverse_correct (x : M31Exact) (hx : x ≠ 0) : baseInverse x = x⁻¹ := by
  have hz : x.val ≠ 0 := by
    intro h
    have he : (x.val : M31Exact) = x := ZMod.natCast_zmod_val x
    rw [h,Nat.cast_zero] at he
    exact hx he.symm
  have h := InverseChain.wordChain_inverse ⟨x.val,ZMod.val_lt x⟩ hz
  simpa [baseInverse,InverseChain.decode] using h

def complexNorm (x : CM31Exact) : M31Exact := x.re*x.re+x.im*x.im
def complexInverse (x : CM31Exact) : CM31Exact :=
  let n := baseInverse (complexNorm x)
  ⟨x.re*n,(-x.im)*n⟩

theorem complex_norm_eq (x : CM31Exact) : complexNorm x = QuadraticAlgebra.norm x := by
  simp [complexNorm,QuadraticAlgebra.norm_def]

theorem complex_norm_nonzero (x : CM31Exact) (hx : x ≠ 0) : complexNorm x ≠ 0 := by
  rw [complex_norm_eq]
  exact fun h => hx (QuadraticAlgebra.norm_eq_zero_iff_eq_zero.mp h)

theorem complex_inverse_correct (x : CM31Exact) (hx : x ≠ 0) :
    complexInverse x = x⁻¹ := by
  unfold complexInverse
  rw [base_inverse_correct _ (complex_norm_nonzero x hx),complex_norm_eq]
  apply QuadraticAlgebra.ext <;> simp [QuadraticAlgebra.inv_def,mul_comm]

def quarticNorm (x : QM31Exact) : CM31Exact := x.re*x.re-qm31R*(x.im*x.im)
def quarticInverse (x : QM31Exact) : QM31Exact :=
  let n := complexInverse (quarticNorm x)
  ⟨x.re*n,(-x.im)*n⟩
def tryInverse (x : QM31Exact) : Option QM31Exact :=
  if x = 0 then none else some (quarticInverse x)

theorem quartic_norm_eq (x : QM31Exact) : quarticNorm x = QuadraticAlgebra.norm x := by
  simp [quarticNorm,QuadraticAlgebra.norm_def,mul_assoc]

theorem quartic_norm_nonzero (x : QM31Exact) (hx : x ≠ 0) : quarticNorm x ≠ 0 := by
  rw [quartic_norm_eq]
  exact fun h => hx (QuadraticAlgebra.norm_eq_zero_iff_eq_zero.mp h)

theorem quartic_inverse_correct (x : QM31Exact) (hx : x ≠ 0) :
    quarticInverse x = x⁻¹ := by
  unfold quarticInverse
  rw [complex_inverse_correct _ (quartic_norm_nonzero x hx),quartic_norm_eq]
  apply QuadraticAlgebra.ext <;> simp [QuadraticAlgebra.inv_def,mul_comm]

theorem try_inverse_none (x : QM31Exact) : tryInverse x = none ↔ x = 0 := by
  simp [tryInverse]

theorem try_inverse_some (x : QM31Exact) (hx : x ≠ 0) :
    tryInverse x = some x⁻¹ := by
  simp [tryInverse,hx,quartic_inverse_correct x hx]

def circleMap (t : QM31Exact) : Except SamplerCirclePolicy.MapError (QM31Exact × QM31Exact) :=
  match tryInverse (1+t*t) with
  | none => .error .singular
  | some n => if t.im = 0 then .error .subfield else .ok ((1-t*t)*n,(t+t)*n)

theorem circle_map_correct (t : QM31Exact) : circleMap t = SamplerCirclePolicy.pureMap t := by
  by_cases h : 1+t*t = 0
  · simp [circleMap,tryInverse,h,SamplerCirclePolicy.pureMap,pow_two]
  · rw [circleMap,try_inverse_some _ h]
    simp [SamplerCirclePolicy.pureMap,pow_two,h,SamplerCirclePolicy.point,
      AspisV8R15.CircleChord.px,AspisV8R15.CircleChord.py,div_eq_mul_inv,two_mul]

def chainAccept (xs : List Nat) : Option (QM31Exact × QM31Exact) :=
  (circleMap (SamplerFieldDecode.decode xs)).toOption

theorem chain_accept_eq : chainAccept = SamplerCirclePolicy.accept := by
  funext xs
  simp only [chainAccept,SamplerCirclePolicy.accept,circle_map_correct]

def chainCircleProgram (s : SourceDuplexStep.State) :=
  BoundedSamplerWrapper.program chainAccept SamplerWrapperPolicies.Error.challengeExhausted
    SamplerWrapperPolicies.Error.parameterExhausted 3 s

theorem chain_circle_program_eq (s : SourceDuplexStep.State) :
    chainCircleProgram s = SamplerCirclePolicy.circleProgram s := by
  unfold chainCircleProgram
  rw [chain_accept_eq]
  rfl

theorem chain_circle_law (s : SourceDuplexStep.State) :
    SamplerOracleLaws.CorrectLaw (chainCircleProgram s)
      (fun H => SamplerCirclePolicy.circleRun H s) := by
  rw [chain_circle_program_eq]
  exact SamplerCirclePolicy.circle_law s

#print axioms base_inverse_correct
#print axioms complex_norm_eq
#print axioms complex_norm_nonzero
#print axioms complex_inverse_correct
#print axioms quartic_norm_eq
#print axioms quartic_norm_nonzero
#print axioms quartic_inverse_correct
#print axioms try_inverse_none
#print axioms try_inverse_some
#print axioms circle_map_correct
#print axioms chain_accept_eq
#print axioms chain_circle_program_eq
#print axioms chain_circle_law
end
end AspisV8R19.NormInverse
