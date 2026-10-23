import Port3_NativeFlushBody
import Port3_FlushInstall
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4D_FlushABI
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2
abbrev K := aspis_core.field.QM31
abbrev FinishIter := Port3_NativeFlushBody.Enum
abbrev FinishBack := FinishIter → FinishIter
abbrev FinishSlice := Slice K
abbrev FinishNextBack := FinishIter → Option (Usize × K) → FinishIter
abbrev FinishIterMut := core.slice.iter.IterMut K
/-- TrustedStd content interpretation of the current emitted mutable ABI.
The outer back closure consumes the final deferred back function. -/
def next (self : FinishIter) : Result (Option (Usize × K) × FinishIter × FinishNextBack) := do
  let (value, iter, back) ← core.slice.iter.IteratorIterMut.next self.iter
  match value with
  | none => ok (none, { self with iter }, fun current _ =>
      { current with iter := back current.iter none })
  | some value => do
    let count ← self.count + 1#usize
    ok (some (self.count, value), { iter, count }, fun current replacement =>
      { current with iter := back current.iter (replacement.map Prod.snd) })
def enumerate (iter : FinishIterMut) : Result (FinishIter × (FinishBack → FinishIterMut)) :=
  ok (⟨iter,0#usize⟩, fun back => (back ⟨iter,0#usize⟩).iter)
def std : Port3_NativeFlushBody.Ops := ⟨next,enumerate⟩
def prefixWrite (f : Nat → K) (start n : Nat) : FinishSlice → FinishSlice
  | s => match n with
    | 0 => s
    | k + 1 => prefixWrite f start k (if start ≤ k then s.setAtNat k (f k) else s)

theorem prefixWrite_before (f : Nat → K) (start n : Nat)
    (h : n ≤ start) (s : FinishSlice) : prefixWrite f start n s = s := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [prefixWrite]
      have hn : ¬ start ≤ n := by omega
      simp only [hn, ite_false]
      exact ih (by omega)

def BackPrefix (f : Nat → K) (start processed : Nat)
    (back : FinishBack) : Prop :=
  ∀ e : FinishIter, (back e).iter.slice = prefixWrite f start processed e.iter.slice

theorem backPrefix_id (f : Nat → K) (start : Nat) :
    BackPrefix f start start (fun e => e) := by
  intro e
  exact prefixWrite_before f start start (Nat.le_refl _) e.iter.slice |>.symm

theorem backPrefix_step (f : Nat → K)
    (start processed : Nat) (back : FinishBack) (index : Std.Usize)
    (nextBack : FinishIter → Option (Std.Usize × K) → FinishIter)
    (hback : BackPrefix f start processed back)
    (hindex : index.val = processed)
    (hstart : start ≤ processed)
    (hwrite : ∀ e : FinishIter,
      (nextBack e (some (index, f index.val))).iter.slice =
        e.iter.slice.setAtNat index.val (f index.val)) :
    BackPrefix f start (processed + 1)
      (fun e => back (nextBack e (some (index, f index.val)))) := by
  intro e
  rw [hback, hwrite]
  simp only [prefixWrite, if_pos hstart, hindex]

#print axioms prefixWrite_before
#print axioms backPrefix_id
#print axioms backPrefix_step
end AspisR1.Port4D_FlushABI
end
