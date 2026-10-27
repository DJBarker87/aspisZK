import XRp_ReverseBodies
open Aeneas Aeneas.Std Result ControlFlow
set_option autoImplicit false
namespace XRp_ReversePass
open XRp_ReverseStep XRp_ReverseBodies
abbrev State := Iter × Back × U64
def step (s : State) := body s.1 s.2.1 s.2.2
def limbs (n : Nat) : List U32 := [2147483647#u32] ++ List.replicate n 0#u32
theorem bound (n : Nat) (h : n ≤ 7) : (limbs n).length ≤ Usize.max := by
  have hm : 8 ≤ Usize.max := by scalar_tac
  simp only [limbs, List.length_append, List.length_singleton, List.length_replicate]
  omega
def state (n : Nat) (h : n ≤ 7) := mk (limbs n) (bound n h)
def finish : (n : Nat) → n ≤ 7 → Back → Back
  | 0,h,b => fun r => b (restore (state 0 h) 2147483647#u32 r)
  | n+1,h,b => finish n (by omega) (fun r => b (restore (state (n+1) h) 0#u32 r))

theorem loop_pass (n : Nat) (h : n ≤ 7) (back : Back) :
    loop step (state n h, back, 0#u64) = ok (0#u64,finish n h back) := by
  induction n generalizing back with
  | zero =>
    rw [loop.eq_def]
    have hp := prime [] (bound 0 h) (by simp) back
    change body (state 0 h) back 0#u64 = _ at hp
    change (match body (state 0 h) back 0#u64 with
      | ok (.cont s) => loop step s
      | ok (.done v) => ok v
      | fail e => fail e
      | div => div) = _
    rw [hp,loop.eq_def]
    have he := empty (fun r => back (restore (state 0 h) 2147483647#u32 r)) 0#u64
    simpa only [step,finish] using congrArg
      (fun cf => match cf with
        | ok (.cont s) => loop step s
        | ok (.done v) => ok v
        | fail e => fail e
        | div => div) he
  | succ n ih =>
    have hn : n ≤ 7 := by omega
    have hl : limbs (n+1) = limbs n ++ [0#u32] := by
      simp [limbs,List.replicate_succ',List.append_assoc]
    have hz := zero (limbs n) (by rw [← hl]; exact bound (n+1) h) (bound n hn) back
    have hs : mk (limbs n ++ [0#u32]) (by rw [← hl]; exact bound (n+1) h) = state (n+1) h := by
      apply congrArg (fun xs : Slice U32 => (⟨⟨xs,0⟩⟩ : Iter))
      apply Subtype.ext
      exact hl.symm
    rw [hs] at hz
    rw [loop.eq_def]
    change (match body (state (n+1) h) back 0#u64 with
      | ok (.cont s) => loop step s
      | ok (.done v) => ok v
      | fail e => fail e
      | div => div) = _
    rw [hz]
    exact ih hn _

#print axioms bound
#print axioms loop_pass
end XRp_ReversePass
