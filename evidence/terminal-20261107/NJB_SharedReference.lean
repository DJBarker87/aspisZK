import NJB_PackLaw
import NJB_StateUpdates
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJB_SharedReference
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode K)
def group (g : Fin 9) : Fin 24 := ⟨12+g.val,by omega⟩
def lanes (v : Fin 33 → NQ) (g : Fin 9) (slot : Fin 4) : NQ :=
 let source := 4*(group g).val+slot.val
 if h : 49≤source ∧ source<82 then v ⟨source-49,by omega⟩ else FIq_Native.field.QM31.ZERO
theorem lanes_canonical (v : Fin 33 → NQ) (hv : ∀ i,Canon (v i)) (g : Fin 9) (slot : Fin 4) :
 Canon (lanes v g slot) := by
 dsimp only [lanes]
 split
 · exact hv _
 · exact FIv_NativeValue.zero.1
def step (v : Fin 33 → NQ) (selector : NQ) (g : Fin 9) (s : Fin 24 → NQ) : Result (Fin 24 → NQ) := do
 let packed ← NJB_PackLaw.reference (lanes v g)
 NJB_StateUpdates.mulAdd s (group g) selector packed
def stepModel (v : Fin 33 → NQ) (selector : NQ) (g : Fin 9) (s : Fin 24 → K) : Fin 24 → K :=
 NJB_StateUpdates.addModel s (group g) (decode selector*NJB_PackLaw.model (lanes v g))
theorem step_result (v : Fin 33 → NQ) (selector : NQ) (g : Fin 9) (s : Fin 24 → NQ)
 (hv : ∀ i,Canon (v i)) (hc : Canon selector) (hs : NJB_StateUpdates.canonical s) :
 ∃ out,step v selector g s=ok out ∧ NJB_StateUpdates.canonical out ∧
 NJB_StateUpdates.decoded out=stepModel v selector g (NJB_StateUpdates.decoded s) := by
 obtain ⟨p,cp,hp,vp⟩ := NJB_PackLaw.result (lanes v g) (lanes_canonical v hv g)
 obtain ⟨out,co,ho,vo⟩ := NJB_StateUpdates.mul_add_result s (group g) selector p hs hc hp
 refine ⟨out,?_,ho,?_⟩
 · simp only [step,cp,co,bind_tc_ok]
 · simpa only [stepModel,vp] using vo
def reference (v : Fin 33 → NQ) (selector : NQ) (s : Fin 24 → NQ) : Result (Fin 24 → NQ) :=
 NJB_StateUpdates.run (step v selector) (List.finRange 9) s
theorem result (v : Fin 33 → NQ) (selector : NQ) (s : Fin 24 → NQ)
 (hv : ∀ i,Canon (v i)) (hc : Canon selector) (hs : NJB_StateUpdates.canonical s) :
 ∃ out,reference v selector s=ok out ∧ NJB_StateUpdates.canonical out ∧
 NJB_StateUpdates.decoded out=(List.finRange 9).foldl
  (fun state g=>stepModel v selector g state) (NJB_StateUpdates.decoded s) :=
 NJB_StateUpdates.run_result _ _ _ s hs (fun g _ before hb=>step_result v selector g before hv hc hb)
#print result
#print axioms lanes_canonical
#print axioms step_result
#print axioms result
end AspisR1.NJB_SharedReference
end
