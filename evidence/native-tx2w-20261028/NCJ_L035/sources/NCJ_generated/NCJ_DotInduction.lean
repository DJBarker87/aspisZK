import NBQ_PublicInvariant
set_option autoImplicit false
noncomputable section
namespace NCJ_DotInduction
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues
abbrev State := NBQ_PublicInvariant.State
abbrev Pair := NE × NQ

def go : List Pair → State → Result (core.result.Result Unit FIo_Native.verifier.Error × State)
  | [],s => ok (.Ok (),s)
  | (v,q)::xs,s => do
    let (r,next) ← FIo_Native.fast_pairing.EbyKDot.push s v q
    match r with
    | .Ok () => go xs next
    | .Err () => ok (.Err .Parse,next)

/-- Every callee cap and invariant is derived from the preceding SAME state,
for any source dot size ≤64, including 64/16/4. No push success is assumed. -/
theorem source (xs : List Pair) (s : State) (invariant : NBQ_PublicInvariant.Inv s)
    (cap : s.count.val+xs.length≤64)
    (canonical : ∀ p∈xs,canonE p.1 ∧ canonQ p.2) :
    ∃ out,go xs s=ok (.Ok (),out) ∧ NBQ_PublicInvariant.Inv out ∧
      out.count.val=s.count.val+xs.length := by
  induction xs generalizing s with
  | nil => exact ⟨s,rfl,invariant,by simp⟩
  | cons p xs ih =>
    rcases p with ⟨v,q⟩
    have hc := canonical (v,q) (by simp)
    have below : s.count.val<4096 := by simp only [List.length_cons] at cap;omega
    obtain ⟨next,step,inv,count⟩ := NBQ_PublicInvariant.step s v q invariant below hc.1 hc.2
    obtain ⟨out,run,io,co⟩ := ih next inv (by simp only [List.length_cons] at cap;omega)
      (fun p hp=>canonical p (by simp [hp]))
    refine ⟨out,?_,io,?_⟩
    · simp only [go,step,bind_tc_ok,run]
    · simp only [List.length_cons];omega

theorem initial (xs : List Pair) (cap : xs.length≤64)
    (canonical : ∀ p∈xs,canonE p.1 ∧ canonQ p.2) :
    ∃ start finish out,
      FIo_Native.fast_pairing.EbyKDot.new=ok start ∧
      go xs start=ok (.Ok (),finish) ∧ finish.count.val=xs.length ∧
      NBQ_PublicInvariant.Inv finish ∧
      FIo_Native.fast_pairing.EbyKDot.finish finish=ok out ∧ canonE out := by
  obtain ⟨start,new,inv⟩ := NBQ_PublicInvariant.initial
  have zero : start.count.val=0 := by
    have same := Result.ok.inj (new.symm.trans NBQ_U06.new)
    rw [same];rfl
  obtain ⟨finish,run,valid,count⟩ := source xs start inv (by omega) canonical
  obtain ⟨out,finished,co⟩ := NBQ_U06.finish finish
  exact ⟨start,finish,out,new,run,by omega,valid,finished,co⟩

#print axioms source
#print axioms initial
end NCJ_DotInduction
