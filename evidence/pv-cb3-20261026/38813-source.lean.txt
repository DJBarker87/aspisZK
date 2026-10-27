import R1Z.PV_CB3_GammaRange
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB3_GammaNonzero
open Aeneas Aeneas.Std Result ProverRwFull

def zeroQM31 : aspis_core.field.QM31 :=
  {c0:={a:=0#u32,b:=0#u32},c1:={a:=0#u32,b:=0#u32}}
def zero : aspis_core.field.wide_exact.WideExact := {c0:=zeroQM31,c1:=zeroQM31}

theorem rank_zero : PV_CB3_StagedGammaRank.outputRank zero = 0 := by rfl

theorem nonzero (block : Array U8 32#usize) : PV_CB3_StagedGammaRank.result block ≠ zero := by
  intro hz
  have hp := PV_CB3_GammaRange.positive block
  rw [hz,rank_zero] at hp
  omega

theorem source_nonzero (block : Array U8 32#usize) :
    PV_CB3_StagedSource.staged_reference.gamma block ≠ ok zero := by
  rw [PV_CB3_StagedGammaRank.source]
  intro hz
  exact nonzero block (Result.ok.inj hz)
#print axioms rank_zero
#print axioms nonzero
#print axioms source_nonzero
end R1Z.PV_CB3_GammaNonzero
