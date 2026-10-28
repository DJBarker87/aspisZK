import NCE_OpeningRead
import MultiproofConeRootGuard

set_option autoImplicit false
noncomputable section
namespace AspisR1.NCE_VerifierCuts
open Aeneas Aeneas.Std MultiproofConeRef NCE_OpeningCuts
abbrev Digest := MultiproofConePhysicalLive.Digest
abbrev Entry := Carrier → Nat → Bool → Bool × Carrier
abbrev Exit := Carrier → Usize → Carrier
abbrev Finish := Carrier → Digest → Slice U8 → Bool × Carrier
attribute [local instance] Classical.propDecidable

/-- Phase-selected ONE control step: entry after the actual well-formed
callee Boolean, row exhaustion n=w, or final n/index/root/cursor guard.
Entry does NOT assert or assume that the child Boolean is true. Its native
well-formed iterator association remains a separate required local cut.
Each control step preserves the SAME Prepared/proof/log and exterior scratch. -/
def NCE_Native_Verifier (entry : Entry) (exit : Exit) (finish : Finish) : Prop :=
  (∀ s bytes valid, bytes ≤ 5504 →
    entry s bytes valid =
      (decide (0 < s.scratch.n.val ∧ s.scratch.n.val ≤ 16 ∧ bytes%32=0) && valid,s)) ∧
  (∀ s w, w.val ≤ 16 → exit s w = {s with scratch:={s.scratch with n:=w}}) ∧
  (∀ s root physical, s.scratch.n.val ≤ 16 → s.scratch.«at».val ≤ physical.val.length →
    physical.val.length ≤ 5504 →
    finish s root physical =
      (decide (s.scratch.n.val=1 ∧ s.scratch.idx.val[0]!.val=0 ∧
        s.scratch.val.val[0]! = root ∧ s.scratch.«at».val=physical.val.length),s))

/-- Entry cannot manufacture success when its actual child rejects. -/
theorem rejected_entry (entry : Entry) (exit : Exit) (finish : Finish)
    (cut : NCE_Native_Verifier entry exit finish) (s : Carrier) (bytes : Nat)
    (size : bytes ≤ 5504) : entry s bytes false = (false,s) := by
  rw [cut.1 s bytes false size]
  simp only [Bool.and_false]

/-- An exhausted row changes only n; old row bytes and all chronological
reads are retained. No next-level success is assumed. -/
theorem level_exit (entry : Entry) (exit : Exit) (finish : Finish)
    (cut : NCE_Native_Verifier entry exit finish) (s : Carrier) (w : Usize)
    (bound : w.val ≤ 16) :
    (exit s w).scratch.idx = s.scratch.idx ∧
    (exit s w).scratch.val = s.scratch.val ∧
    (exit s w).scratch.«at» = s.scratch.«at» ∧
    (exit s w).scratch.n = w ∧ (exit s w).prepared = s.prepared ∧
    (exit s w).proof = s.proof ∧ (exit s w).log = s.log := by
  rw [cut.2.1 s w bound]
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Reuse the existing root/cursor theorem at the SAME final scratch. This
is a final-control cut, not a whole multiproof or accepted-root assumption. -/
theorem finish_model (entry : Entry) (exit : Exit) (finish : Finish)
    (cut : NCE_Native_Verifier entry exit finish) (s : Carrier) (root : Digest)
    (physical : Slice U8) (small : s.scratch.n.val ≤ 16)
    (cursor : s.scratch.«at».val ≤ physical.val.length) (size : physical.val.length ≤ 5504) :
    finish s root physical =
      (MultiproofConeRootGuard.modelRoot (AspisV8R19.SqueezeOracleBridge.decodeState root)
        (some (MultiproofConePhysicalViews.live s.scratch 0 s.scratch.n.val,
          MultiproofConePhysicalViews.remaining physical s.scratch.«at»)),s) := by
  rw [cut.2.2 s root physical small cursor size]
  exact congrArg (fun accepted => (accepted,s))
    (MultiproofConeRootGuard.root_guard root physical s.scratch cursor)

#print axioms rejected_entry
#print axioms level_exit
#print axioms finish_model
end AspisR1.NCE_VerifierCuts
end
