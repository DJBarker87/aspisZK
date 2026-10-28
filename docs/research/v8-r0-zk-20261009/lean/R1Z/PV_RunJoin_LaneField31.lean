import R1Z.PV_RunJoin_LaneFold31
import R1Z.PV_Src_PortNodeResult
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_LaneField31
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_RunJoin_LaneFold31
local instance : BuilderForestAdmissionPort.ExternalLinear := PV_Src_ExternalReference.dictionary
variable {K : Type} [Field K] [CharP K 2147483647]
attribute [local irreducible] R0P.nodeCompress R0P.poseidonPermutation

def fieldFold (sibling : Nat → R0P.Digest K) (reverse : Nat → Bool) :
    List Nat → R0P.Digest K → R0P.Digest K
  | [], current => current
  | level::levels, current =>
      fieldFold sibling reverse levels
        (if reverse level then R0P.nodeCompress (sibling level) current
         else R0P.nodeCompress current (sibling level))

theorem parent_source (left right : Digest) (hc : Canon8 right) :
    ∃ out, BuilderForestAdmissionPort.pool_v1.format.pool_v1_tree_parent left right = ok out ∧
      Canon8 out ∧ digK (K := K) out = R0P.nodeCompress (digK left) (digK right) := by
  obtain ⟨out,ho,hcanonical,hm⟩ := PV_Src_PortNodeResult.source (K := K) left right (hc 7 (by decide))
  exact ⟨out,ho,hcanonical,funext hm⟩
#print axioms parent_source

theorem step_source (current sibling : Digest) (reverse : Bool)
    (hc : Canon8 current) (hs : Canon8 sibling) :
    ∃ out, step BuilderForestAdmissionPort.pool_v1.format.pool_v1_tree_parent
        current sibling reverse = ok out ∧ Canon8 out ∧
      digK (K := K) out =
        (if reverse then R0P.nodeCompress (digK sibling) (digK current)
         else R0P.nodeCompress (digK current) (digK sibling)) := by
  cases reverse with
  | false => exact parent_source current sibling hs
  | true => exact parent_source sibling current hc
#print axioms step_source

theorem fold_source (sibling : Nat → Digest) (reverse : Nat → Bool)
    (levels : List Nat) (current : Digest) (hc : Canon8 current)
    (hs : ∀ level ∈ levels, Canon8 (sibling level)) :
    ∃ out, fold BuilderForestAdmissionPort.pool_v1.format.pool_v1_tree_parent
        sibling reverse levels current = ok out ∧ Canon8 out ∧
      digK (K := K) out = fieldFold (fun level => digK (sibling level)) reverse levels (digK current) := by
  induction levels generalizing current with
  | nil => exact ⟨current,rfl,hc,rfl⟩
  | cons level levels ih =>
    obtain ⟨next,hnext,hn,hm⟩ := step_source (K := K) current (sibling level) (reverse level) hc (hs level (by simp))
    obtain ⟨out,hout,ho,hl⟩ := ih next hn (fun l h => hs l (by simp only [List.mem_cons]; exact Or.inr h))
    refine ⟨out,?_,ho,?_⟩
    · rw [fold,hnext]
      exact hout
    · rw [fieldFold,← hm]
      exact hl
#print axioms fold_source
end R1Z.PV_RunJoin_LaneField31
