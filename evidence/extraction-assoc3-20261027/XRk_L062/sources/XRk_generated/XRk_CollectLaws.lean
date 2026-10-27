import XRk_ResultTools
open Aeneas Aeneas.Std Result
namespace XRk_CollectLaws
open XRk_ResultTools
def step {T : Type} (call : Nat → Result (Option T)) (seed : Option (List T)) (i : Nat) : Result (Option (List T)) := do
  match seed with
  | none => ok none
  | some xs =>
    let value ← call i
    ok (value.map (fun v => xs ++ [v]))
theorem none_absorbing {T : Type} (call : Nat → Result (Option T)) (indices : List Nat) :
    indices.foldlM (step call) none = ok none := by
  induction indices with
  | nil => rfl
  | cons i tail ih => simpa only [List.foldlM_cons,step,bind_tc_ok] using ih

theorem length_of_success {T : Type} (call : Nat → Result (Option T)) (indices : List Nat)
    (seed out : List T) (run : indices.foldlM (step call) (some seed) = ok (some out)) :
    out.length = seed.length + indices.length := by
  induction indices generalizing seed with
  | nil =>
    have same : seed=out := Option.some.inj (Result.ok.inj run)
    simp only [same,List.length_nil,Nat.add_zero]
  | cons i tail ih =>
    simp only [List.foldlM_cons,step,bind_tc_ok] at run
    obtain ⟨value,_,run⟩ := bind_success _ _ _ run
    cases value with
    | none =>
      change tail.foldlM (step call) none = ok (some out) at run
      rw [none_absorbing] at run
      cases run
    | some value =>
      change tail.foldlM (step call) (some (seed++[value])) = ok (some out) at run
      have h := ih (seed++[value]) run
      simpa only [List.length_append,List.length_singleton,List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
#print axioms none_absorbing
#print axioms length_of_success
end XRk_CollectLaws
