import FJf_CommonStep
import FJc_SharedSelf
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJf_CommonValue
open Aeneas Aeneas.Std Result
open AspisR1Stage2 AspisR1Stage2.Stage2Finish
open FIo_FieldBridge (NQ)
open FJf_CommonStep

theorem loop (alpha : Array K 10#usize) (z : Array aspis_core.circle.SecureCirclePoint 2#usize)
    (w : FIo_Install.W)
    (hc : FJc_WeightArray.canonical (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ alpha))
    (hw : FIn_WeightsInstall.newWeights .S2 alpha z=ok (.Ok w))
    (iter : FIo_RangeNext.Range) (common : Array NQ 16#usize) (out : ResultType)
    (inv : Inv (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ alpha) (iter,common))
    (run : FIo_Native.weights.Weights.pair_loop1 iter (FIo_Install.toWeights w) common=ok out) :
    Post (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ alpha) out := by
  exact FIo_LoopInvariant.preserve
    (fun t : State => FIo_Native.weights.Weights.pair_loop1.body (FIo_Install.toWeights w) t.1 t.2)
    (Inv (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ alpha))
    (Post (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ alpha)) measure
    (fun t h r hr => by cases r <;> exact step alpha z w hc hw t h _ hr)
    (iter,common) out inv run

theorem sixteen (alpha : Array K 10#usize) (z : Array aspis_core.circle.SecureCirclePoint 2#usize)
    (w : FIo_Install.W)
    (hc : FJc_WeightArray.canonical (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ alpha))
    (hw : FIn_WeightsInstall.newWeights .S2 alpha z=ok (.Ok w)) (out : ResultType)
    (run : FIo_Native.weights.Weights.pair_loop1 {start:=0#usize,«end»:=16#usize}
      (FIo_Install.toWeights w) (Array.repeat 16#usize FIo_Native.aspis_core.field.QM31.ZERO)=ok out) :
    out.1=FIo_Install.toWeights w ∧ Post (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ alpha) out := by
  refine ⟨FJc_SharedSelf.value _ out.1 _ _ out.2 run,?_⟩
  exact loop alpha z w hc hw _ _ out
    ⟨FJf_QMArray.zeros _,rfl,by change (0:Nat)≤16;decide,by intro j hj;change j < 0 at hj;omega⟩ run
#print axioms loop
#print axioms sixteen
end AspisR1.FJf_CommonValue
end
