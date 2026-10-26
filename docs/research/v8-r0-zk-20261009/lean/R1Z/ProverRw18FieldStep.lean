import R1Z.ProverRw18FieldMeaning
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw18FieldStep
open Aeneas Aeneas.Std Result ProverRw18FieldMeaning

theorem step (out power lambda : Raw) (value : U32)
    (hout : Canonical out) (hpower : Canonical power) (hlambda : Canonical lambda) :
    ∃ out1 power1 : Raw,
      PV_RW_CompressConcrete.owned (full out) (full power) value (full lambda)=
        ok (full out1,full power1) ∧
      Canonical out1 ∧ Canonical power1 ∧
      decode out1=decode out+decode power*(value.val : K) ∧
      decode power1=decode power*decode lambda := by
  obtain ⟨scaled,hs,hcs,hds⟩ := ProverRw18FieldMeaning.scale power value
  obtain ⟨out1,ho,hco,hdo⟩ := ProverRw18FieldMeaning.add out scaled hout hcs
  obtain ⟨power1,hp,hcp,hdp⟩ := ProverRw18FieldMeaning.mul power lambda hpower hlambda
  refine ⟨out1,power1,?_,hco,hcp,?_,hdp⟩
  · simp only [PV_RW_CompressConcrete.owned,hs,ho,hp,bind_tc_ok]
  · rw [hdo,hds]

#print axioms step
end R1Z.ProverRw18FieldStep
