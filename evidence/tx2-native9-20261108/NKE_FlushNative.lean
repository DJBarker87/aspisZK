import NKE_Stores
set_option autoImplicit false
noncomputable section
namespace NKE_FlushNative
open Aeneas Aeneas.Std Result AspisR1
abbrev K := VTop_Stages.aspis_core.field.QM31
abbrev BW := VTop_Stages.verifier.BatchedWeights
/-- At the same receiver, the CLOSED value child determines each reply.
The fold still executes one store, including every unselected cell. -/
def states (pending : BW) (weights : Slice K) (n : Nat) : List K :=
 NKE_Stores.G (pending.raw.val.map NJJ_Flush.cell) weights.val n

theorem step (pending : BW) (weights : Slice K)
 (rawSize : pending.raw.val.length=64) (weightSize : weights.val.length=64)
 (i : Nat) (inside : i<64) (reply : K)
 (child : (pending.raw.val[i]?).map NJJ_Flush.cell=some reply) :
 NJR_Cuts.flushStep pending.raw.val pending.raw.val pending.terms pending.terms
 (states pending weights i) (states pending weights (i+1)) i reply := by
 refine ⟨rfl,rfl,?_,?_⟩
 · simp only [states,NKE_Stores.length]
 · intro j hj
   have hi : i<weights.val.length := by omega
   have h := NKE_Stores.step (pending.raw.val.map NJJ_Flush.cell) weights.val
    (by simp only [List.length_map,rawSize,weightSize]) i hi j
    (by simpa only [states,NKE_Stores.length] using hj)
   simpa only [states,List.getElem?_map,child] using h

theorem source (pending : BW) (weights : Slice K)
 (rawSize : pending.raw.val.length=64) (weightSize : weights.val.length=64) :
 Port3_FlushInstall.flush pending weights=ok (NJJ_Flush.output pending) ∧
 states pending weights 64=(NJJ_Flush.output pending).val ∧
 (∀ q∈states pending weights 64,Port3_FlushInstall.Canonical q) := by
 apply NJR_FlushComposition.source pending weights rawSize weightSize (states pending weights)
 · intro n _
   simpa only [states,NKE_Stores.length] using weightSize
 · intro i hi j hj
   have h := NKE_Stores.step (pending.raw.val.map NJJ_Flush.cell) weights.val
    (by simp only [List.length_map,rawSize,weightSize]) i (by omega) j (by omega)
   simpa only [states,List.getElem?_map] using h
#print axioms step
#print axioms source
end NKE_FlushNative
