import R1Z.PV_RW_CompressConcrete
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RW_CompressPowerStep
open Aeneas Aeneas.Std Result ProverRwDictionaryTower
abbrev Q := ProverRwFull.aspis_core.field.QM31

theorem image (out power : Q) (value : U32) (lambda : Q) :
    ∃ nextOut nextPower,
      PV_RW_CompressConcrete.step out power value lambda=ok (nextOut,nextPower) ∧
      qMul power lambda=ok nextPower := by
  obtain ⟨scaled,hs⟩ := ProverRwP7CompressPrimitives.Native.q_scale (toQ power) value
  obtain ⟨nextOut,ho⟩ := ProverRwP6QuarticTotal.add (toQ out) (toQ (fromQ scaled))
  obtain ⟨nextPower,hp⟩ := ProverRwP6QuarticTotal.mul (toQ power) (toQ lambda)
  refine ⟨fromQ nextOut,fromQ nextPower,?_,?_⟩
  · rw [PV_RW_CompressConcrete.current_owned]
    simp only [PV_RW_CompressConcrete.owned,hs,qAdd,qMul,ho,hp,mapResult,bind_tc_ok]
  · simp only [qMul,hp,mapResult]

theorem projection (out power : Q) (value : U32) (lambda : Q) :
    mapResult Prod.snd (PV_RW_CompressConcrete.step out power value lambda)=qMul power lambda := by
  obtain ⟨nextOut,nextPower,hs,hp⟩ := image out power value lambda
  rw [hs,hp]
  rfl
#print axioms image
#print axioms projection
end R1Z.PV_RW_CompressPowerStep
