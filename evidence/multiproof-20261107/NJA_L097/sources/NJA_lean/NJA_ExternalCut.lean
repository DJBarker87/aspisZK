import NJA_External
import NJA_Mat4Cut
import NJA_PointStaging

set_option autoImplicit false
noncomputable section
namespace NJA_ExternalCut
open Aeneas Aeneas.Std Result
open NJA_ChunkFrame
abbrev K := NJA_Matrix.K
abbrev Event := NJA_Pow5Cut.Event

-- Exact per-cell log/window facts, plus start and one native write transition.
-- No final buffer/model equality is a premise.
structure Cut (v : State U32) (events : Fin 16 → Event) (steps : Nat → State U32) where
 start : steps 0=v
 args : ∀ i, (events i).kind=1 ∧ (events i).a=NJA_External.arg v i ∧ (events i).b=0
 next : ∀ (n : Nat) (h : n<16), ∀ k,
   steps (n+1) k = if k=⟨n,h⟩ then (events ⟨n,h⟩).out else steps n k

def CalleeLaws (events : Fin 16 → Event) : Prop :=
 ∀ i, (events i).out.val=(events i).a%2147483647

theorem domains (v : State U32) (events : Fin 16 → Event) (steps : Nat → State U32)
 (cut : Cut v events steps) : ∀ i, (events i).a<2^62 := by
 intro i
 rw [(cut.args i).2.1]
 exact NJA_External.arg_bound v i

theorem result (input v : State U32) (events : Fin 16 → Event) (steps : Nat → State U32)
 (cut : Cut v events steps) (laws : CalleeLaws events)
 (blocks : ∀ g c, ((v (pack g c)).val:K) =
   R0P.poseidonMat4 (fun j => ((input (pack g j)).val:K)) c) :
 ∀ i, (steps 16 i).val<2147483647 ∧
 ((steps 16 i).val:K)=R0P.poseidonExternalLinear (fun j => ((input j).val:K)) i := by
 have final := NJA_PointStaging.complete v (fun i _ => (events i).out) steps cut.start cut.next
 rw [final]
 intro i
 have hr := NJA_Mat4Cut.reduction_determined (NJA_External.word v i) (events i).out (by
   rw [NJA_External.word_value]
   simpa only [(cut.args i).2.1] using laws i)
 obtain ⟨z,hz,cz,vz⟩ := NJA_External.callee v i
 have eq : z=(events i).out := Result.ok.inj (hz.symm.trans hr)
 rw [eq] at cz vz
 exact ⟨cz,vz.trans (NJA_External.model input v blocks i)⟩

#print axioms domains
#print axioms result
end NJA_ExternalCut
end
