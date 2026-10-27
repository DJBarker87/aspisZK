import R1Z.PV_Inv_SourceBranch
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Inv_SourceTests
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisR1.ExtractedCurrentQM31Exact (decode)
open PV_Inv_SourceBranch

def tests (chi : Old.Q) : List Old.Q → Result (List Bool)
 | [] => ok []
 | x::xs => do
   let b ← branch chi x
   let bs ← tests chi xs
   ok (b::bs)

theorem all_false (chi : Old.Q) (xs : List Old.Q) (hc : Canonical chi)
    (hxs : ∀ x ∈ xs, Canonical x) (hn : ∀ x ∈ xs, decode chi ≠ decode x) :
    tests chi xs=ok (List.replicate xs.length false) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hb := branch_false chi x hc (hxs x (by simp)) (hn x (by simp))
    have ht := ih (fun y hy => hxs y (by simp [hy])) (fun y hy => hn y (by simp [hy]))
    simp only [tests,hb,ht,bind_tc_ok,List.length_cons,List.replicate_succ]

#print axioms all_false
end R1Z.PV_Inv_SourceTests
