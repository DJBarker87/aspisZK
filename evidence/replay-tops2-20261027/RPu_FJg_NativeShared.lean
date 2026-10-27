import RPu_FJg_ConstructorShared
import RPu_FJf_NativeFactors
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJg_NativeShared
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NQ)
abbrev Digit := Array NQ 4#usize

def cell (w : FIo_Native.weights.Weights) (k d : Nat) : Option Digit :=
  w.factors.val[k]?.bind (fun row=>row.val[d]?)

theorem mapped (w : FIo_Install.W) (k d : Nat) :
    cell (FIo_Install.toWeights w) k d=
      (FJg_DigitProvenance.cell w.factors k d).map (FIn_WeightsInstall.mapArray FIo_Install.toQ) := by
  unfold cell FJg_DigitProvenance.cell FIo_Install.toWeights
  simp only [FIn_WeightsInstall.mapArray,List.getElem?_map]
  cases h : w.factors.val[k]? with
  | none => rfl
  | some row =>
    simp only [Option.map_some,Option.bind_some,FIn_WeightsInstall.mapArray,List.getElem?_map]

theorem installed (v : AspisR1Stage2.transport.Variant)
    (alpha : Array AspisR1Stage2.Stage2Finish.K 10#usize)
    (z : Array AspisR1Stage2.aspis_core.circle.SecureCirclePoint 2#usize) (w : FIo_Install.W)
    (run : FIn_WeightsInstall.newWeights v alpha z=ok (.Ok w))
    (d : Nat) (hd : d=2 ∨ d=3) :
    cell (FIo_Install.toWeights w) 0 d=cell (FIo_Install.toWeights w) 2 d := by
  rw [mapped,mapped,FJg_ConstructorShared.source _ _ _ w (FJc_Constructor.source v alpha z w run) d hd]

/-- Native guard reads on the SAME returned installed weights agree exactly. -/
theorem reads (v : AspisR1Stage2.transport.Variant)
    (alpha : Array AspisR1Stage2.Stage2Finish.K 10#usize)
    (z : Array AspisR1Stage2.aspis_core.circle.SecureCirclePoint 2#usize) (w : FIo_Install.W)
    (run : FIn_WeightsInstall.newWeights v alpha z=ok (.Ok w))
    (d : Usize) (hd : d.val=2 ∨ d.val=3)
    (r0 r2 : Array Digit 5#usize) (x y : Digit)
    (h0 : Array.index_usize (FIo_Install.toWeights w).factors 0#usize=ok r0)
    (h2 : Array.index_usize (FIo_Install.toWeights w).factors 2#usize=ok r2)
    (hx : Array.index_usize r0 d=ok x) (hy : Array.index_usize r2 d=ok y) : x=y := by
  have e := installed v alpha z w run d.val hd
  unfold cell at e
  have e0 : (FIo_Install.toWeights w).factors.val[0]?=some r0 := by
    simpa only [show (0#usize).val=0 from by decide] using FJc_ReadSlot.slot _ _ _ h0
  have e2 : (FIo_Install.toWeights w).factors.val[2]?=some r2 := by
    simpa only [show (2#usize).val=2 from by decide] using FJc_ReadSlot.slot _ _ _ h2
  simp only [e0,e2,Option.bind_some,FJc_ReadSlot.slot _ _ _ hx,FJc_ReadSlot.slot _ _ _ hy] at e
  exact Option.some.inj e
#print axioms mapped
#print axioms installed
#print axioms reads
end AspisR1.FJg_NativeShared
end
