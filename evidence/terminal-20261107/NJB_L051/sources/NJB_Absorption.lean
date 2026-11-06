import NJB_AbsorptionLane
import NJB_Traverse
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJB_Absorption
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode K)
theorem size : (16#usize).val=16 := by scalar_tac
def cell (opened : Array NQ 16#usize) (lane : Fin 16) : NQ :=
 opened.val[lane.val]'(by rw [opened.property,size];exact lane.isLt)
def reference (low fixed two eight nodes : NQ) (opened : Array NQ 16#usize) : Result (Array NQ 16#usize) := do
 let scales ← NJB_AbsorptionScales.reference low fixed two eight nodes
 let ys ← NJB_Traverse.run (NJB_AbsorptionLane.reference scales (cell opened)) (List.ofFn (fun lane : Fin 16=>lane))
 ok (Array.make 16#usize ys.val (by simpa only [List.length_ofFn,size] using ys.property))
/-- Full fixed-array Result, not one accepted lane or a successful-child premise.
Native prologue and arbitrary lane cuts are composed through the size-preserving
traversal; every prepared-cache domain and arithmetic law is discharged here. -/
theorem result (low fixed two eight nodes : NQ) (opened : Array NQ 16#usize)
 (hl : Canon low) (hf : Canon fixed) (ht : Canon two) (he : Canon eight) (hn : Canon nodes)
 (ho : FIw_ArrayValue.canonical opened) :
 ∃ out,reference low fixed two eight nodes opened=ok out ∧ FIw_ArrayValue.canonical out ∧
 out.val.map decode=List.ofFn (fun lane : Fin 16=>NJB_AbsorptionLane.literal
  (decode low) (decode fixed) (decode two) (decode eight) (decode nodes) (decode (cell opened lane)) lane) := by
 obtain ⟨scales,call,hs⟩ := NJB_AbsorptionScales.result low fixed two eight nodes hl hf ht he hn
 have hopen (lane : Fin 16) : Canon (cell opened lane) := ho _ (List.getElem_mem _)
 let value := fun lane : Fin 16=>NJB_AbsorptionLane.literal
  (decode low) (decode fixed) (decode two) (decode eight) (decode nodes) (decode (cell opened lane)) lane
 have child (lane : Fin 16) : ∃ out,NJB_AbsorptionLane.reference scales (cell opened) lane=ok out ∧
   Canon out ∧ decode out=value lane := by
  obtain ⟨out,co,hc,vc⟩ := NJB_AbsorptionLane.result scales (cell opened) lane
   (fun i=>⟨(hs i).1,(hs i).2.1⟩) hopen
  refine ⟨out,co,hc,?_⟩
  rw [vc,(hs (NJB_AbsorptionLane.group lane)).2.2]
  exact NJB_AbsorptionLane.model_eq_literal _ _ _ _ _ _ lane
 obtain ⟨ys,cy,hy,vy⟩ := NJB_Traverse.result (NJB_AbsorptionLane.reference scales (cell opened))
  Canon decode value (List.ofFn (fun lane : Fin 16=>lane)) (fun lane _=>child lane)
 refine ⟨Array.make 16#usize ys.val (by simpa only [List.length_ofFn,size] using ys.property),?_,hy,?_⟩
 · simp only [reference,call,cy,bind_tc_ok]
 · change ys.val.map decode=List.ofFn value
   rw [List.map_ofFn] at vy
   exact vy.trans (congrArg (fun f : Fin 16 → K=>List.ofFn f) (funext (fun _=>rfl)))
#print result
#print axioms size
#print axioms result
end AspisR1.NJB_Absorption
end
