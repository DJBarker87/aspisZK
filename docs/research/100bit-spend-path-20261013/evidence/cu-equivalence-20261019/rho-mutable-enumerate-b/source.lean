import AspisR1CuRho.MutableIteratorRuntime

/-! The mutable enumeration interface preserves the existing ordinary
enumerator's value/control behavior after erasing the returned handback.
This is a model compatibility theorem; concrete source admission and the
finish-loop theorem must still bind the selected mutable instance. -/
set_option autoImplicit false
namespace AspisR1.CuSavingsMutableEnumerate
open Aeneas Aeneas.Std Result

def ordinaryAdapter {I Item : Type}
    (inst : AspisR1CuRho.core.iter.traits.iterator.Iterator I Item) :
    Aeneas.Std.core.iter.traits.iterator.Iterator I Item :=
  {next := fun iter => do
    let (value,state,_) ← inst.next iter
    .ok (value,state)}

def erase {I Item : Type}
    (run : Result (Option Item × I × (I → Option Item → I))) : Result (Option Item × I) := do
  let (value,state,_) ← run
  .ok (value,state)

theorem enumerate_control_eq {I Item : Type}
    (inst : AspisR1CuRho.core.iter.traits.iterator.Iterator I Item)
    (self : Aeneas.Std.core.iter.adapters.enumerate.Enumerate I) :
    erase (AspisR1CuRho.core.iter.adapters.enumerate.IteratorEnumerate.next inst self) =
      Aeneas.Std.core.iter.adapters.enumerate.IteratorEnumerate.next (ordinaryAdapter inst) self := by
  unfold erase AspisR1CuRho.core.iter.adapters.enumerate.IteratorEnumerate.next
    Aeneas.Std.core.iter.adapters.enumerate.IteratorEnumerate.next ordinaryAdapter
  cases h : inst.next self.iter with
  | fail e => simp only [h,bind_tc_fail]
  | div => simp only [h,bind_tc_div]
  | ok triple =>
    rcases triple with ⟨value,state,back⟩
    simp only [h,bind_tc_ok]
    cases value with
    | none => rfl
    | some item =>
      simp only [Prod.casesOn,bind_assoc_eq,bind_tc_ok]
      cases hc : UScalar.add self.count 1#usize with
      | fail e => simp only [hc,bind_tc_fail]
      | div => simp only [hc,bind_tc_div]
      | ok count => simp only [hc,bind_tc_ok]

#print axioms enumerate_control_eq
end AspisR1.CuSavingsMutableEnumerate
