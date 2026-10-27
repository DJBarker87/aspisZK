import RPu_FJf_CommonDone
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJf_CommonStep
open Aeneas Aeneas.Std Result ControlFlow
open AspisR1Stage2 AspisR1Stage2.Stage2Finish
open FIo_FieldBridge (NQ)
abbrev State := FIo_RangeNext.Range × Array NQ 16#usize
abbrev ResultType := FIo_Native.weights.Weights × Array NQ 16#usize

def Inv (p : Array FIn_WeightsExtract.field.QM31 10#usize) (t : State) : Prop :=
  FJf_QMArray.canon t.2 ∧ t.1.end.val=16 ∧ t.1.start.val≤16 ∧
  ∀ j,j < t.1.start.val → FJf_QMArray.value t.2 j=FJf_CommonCell.model p j

def Post (p : Array FIn_WeightsExtract.field.QM31 10#usize) (out : ResultType) : Prop :=
  FJf_QMArray.canon out.2 ∧ ∀ j,j < 16 → FJf_QMArray.value out.2 j=FJf_CommonCell.model p j

def measure (t : State) : Nat := t.1.end.val-t.1.start.val

theorem step (alpha : Array K 10#usize) (z : Array aspis_core.circle.SecureCirclePoint 2#usize)
    (w : FIo_Install.W)
    (hc : FJc_WeightArray.canonical (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ alpha))
    (hw : FIn_WeightsInstall.newWeights .S2 alpha z=ok (.Ok w))
    (t : State) (inv : Inv (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ alpha) t)
    (out : ControlFlow State ResultType)
    (run : FIo_Native.weights.Weights.pair_loop1.body (FIo_Install.toWeights w) t.1 t.2=ok out) :
    match out with
    | .done f => Post (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ alpha) f
    | .cont next => Inv (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ alpha) next ∧ measure next < measure t := by
  rcases t with ⟨iter,common⟩
  dsimp only [Inv] at inv
  cases out with
  | done f =>
    obtain ⟨stop,rfl⟩ := FJf_CommonDone.done _ iter common f run
    have eq : iter.start.val=16 := by omega
    exact ⟨inv.1,by simpa only [eq] using inv.2.2.2⟩
  | cont next =>
    rcases next with ⟨cursor,f⟩
    obtain ⟨he,hs,hm,hf,hv⟩ := FJf_CommonCell.value alpha z w hc hw iter cursor common f inv.2.1 inv.1 run
    dsimp only [Inv]
    refine ⟨⟨hf,?_,by omega,?_⟩,?_⟩
    · rw [he];exact inv.2.1
    · intro j hj
      rw [hv]
      by_cases eq : iter.start.val=j
      · rw [if_pos eq]
      · rw [if_neg eq]
        exact inv.2.2.2 j (by omega)
    · simp only [measure,he,hs];omega
#print axioms step
end AspisR1.FJf_CommonStep
end
