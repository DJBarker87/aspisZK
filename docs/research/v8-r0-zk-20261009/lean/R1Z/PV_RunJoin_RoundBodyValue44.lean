import R1Z.PV_RunJoin_RoundCellThread44
import R1Z.PV_RunJoin_RoundStepValue44
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RoundBodyValue44
open Aeneas Aeneas.Std Result ProverRwFull
open ProverCommitWideOps48 ProverCommitMix48 ProverCommitRoundStep48
open PV_RunJoin_FoldCell44 (array)
variable [ExternalTypes]

theorem extract {A B D : Type} (r : Result A) (cursor : B) (out : A)
    (h : (do let v ← r; .ok (.cont (v,cursor) : ControlFlow (A × B) D)) = .ok (.cont (out,cursor))) :
    r = .ok out := by
  cases r with
  | ok x =>
    simp only [bind_tc_ok] at h
    exact congrArg Result.ok (congrArg Prod.fst (ControlFlow.cont.inj (Result.ok.inj h)))
  | fail e => cases h
  | div => cases h

theorem step (ops : ExternalFuns) (count : Usize) (q w xs : Nat → Raw)
    (hq : ∀ k, k < 1024 → canonical (q k)) (hw : ∀ k, k < 1024 → canonical (w k))
    (hxs : ∀ k, k < 7 → canonical (xs k))
    (d s t : Usize) (hd : d.val < 256) (size : 4*d.val + 4 ≤ count.val)
    (hs : s.val < 4) (ht : t.val < 4) :
    ∃ ys : Nat → Raw,
      @PV_RunJoin_RoundCellThread44.step _ (ProverRwP6BodyCandidate.selected ops)
        (Array.to_slice (array count q)) (Array.to_slice (array count w)) d s (array 7#usize xs) t = .ok (array 7#usize ys) ∧
      (∀ k, k < 7 → canonical (ys k)) ∧
      ∀ k, k < 7 → value (ys k) = value (xs k) +
        if k = s.val + perm t.val then value (q (4*d.val+s.val))*value (w (4*d.val+t.val)) else 0 := by
  obtain ⟨ys,hy,hcy,hdy⟩ := PV_RunJoin_RoundStepValue44.step ops count q w xs hq hw hxs d s t hd size hs ht
  refine ⟨ys,?_,hcy,hdy⟩
  exact extract _ (Usize.wrapping_add t 1#usize) _
    ((@PV_RunJoin_RoundCellThread44.one_step _ (ProverRwP6BodyCandidate.selected ops)
      (Array.to_slice (array count q)) (Array.to_slice (array count w)) d s (array 7#usize xs) t ht).symm.trans hy)
#print axioms extract
#print axioms step
end R1Z.PV_RunJoin_RoundBodyValue44
