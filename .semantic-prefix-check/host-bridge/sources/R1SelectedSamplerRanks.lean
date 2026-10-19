import R0P.CircleSampler
import R1OpeningSamplerBound

/-! Concrete positional equivalences for the selected one-block sampler
model. These reuse the old modulo maps; they do not identify Rust execution
with those maps. The index is a positional rank, not a field Nat cast. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.SelectedSamplerRanks
open AspisV8R19.SourceDuplexStep AspisWideTower AspisCircleGroupOrder

def stateRank : State ≃ Fin (2^256) :=
  R0C.ModuloField.blockRank.trans (finCongr (by norm_num))

theorem stateRank_val (s : State) :
    (stateRank s).val = (R0C.ModuloField.blockRank s).val := rfl

theorem ordinary_eq (s : State) :
    OpeningSamplerBound.sample stateRank R0C.ModuloField.fieldRank s =
      R0C.ModuloField.ordinary s := by
  apply congrArg R0C.ModuloField.fieldRank
  apply Fin.ext
  rfl

theorem gamma_eq (s : State) :
    OpeningSamplerBound.gammaSample stateRank R0C.ModuloField.nonzeroRank s =
      R0C.ModuloField.gamma s := by
  unfold OpeningSamplerBound.gammaSample OpeningSamplerBound.gammaNZ
    R0C.ModuloField.gamma R0C.ModuloField.gammaNZ
  congr 1

theorem qm31_eq (s : State) :
    R0P.SemSource.qm31Rank
      (R0C.ModuloCounting.reduce (by norm_num [P]) (stateRank s)) =
      R0P.SemSource.qm31Sample s := by
  apply congrArg R0P.SemSource.qm31Rank
  apply Fin.ext
  rfl

#print axioms stateRank_val
#print axioms ordinary_eq
#print axioms gamma_eq
#print axioms qm31_eq
end AspisR1.SelectedSamplerRanks
end
