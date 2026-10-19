import AspisR1CuIterator.Next

/-! Exact execution shape of the unchanged emitted standard next body at the
selected mutable-slice specialization. Its backward counter is the captured
one; the verifier observes the returned slice rather than that counter. -/
set_option autoImplicit false
namespace AspisR1.CuSavingsIteratorSource
open Aeneas Aeneas.Std Result
open AspisR1CuIterator
variable {T : Type}
abbrev Iter (T : Type) := Aeneas.Std.core.slice.iter.IterMut T
abbrev Enum (T : Type) := AspisR1CuIterator.Enumerate (Iter T)
abbrev next := @AspisR1CuIterator.EnumerateIterMut.Insts.CoreIterTraitsIteratorIteratorPairUsizeMutAT.next

def someBack (self : (Enum T)) (original : T) (inner : (Iter T) → Option T → (Iter T))
    (out : (Enum T)) (value : Option (Usize × T)) : (Enum T) :=
  {self with iter := inner out.iter (some (match value with
    | some (_,x) => x
    | none => original))}

def noneBack (self : (Enum T)) (inner : (Iter T) → Option T → (Iter T))
    (out : (Enum T)) (_ : Option (Usize × T)) : (Enum T) :=
  {self with iter := inner out.iter none}

theorem source_none (self : (Enum T)) (state : (Iter T)) (inner : (Iter T) → Option T → (Iter T))
    (hn : Aeneas.Std.core.slice.iter.IteratorIterMut.next self.iter = .ok (none,state,inner)) :
    next self = .ok (none,{self with iter := state},noneBack self inner) := by
  simp only [next,AspisR1CuIterator.EnumerateIterMut.Insts.CoreIterTraitsIteratorIteratorPairUsizeMutAT.next,
    hn,bind_tc_ok,AspisR1CuIterator.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
    AspisR1CuBorrowOption.core.option.OptionMutAT.Insts.Aspis_cu_borrow_optionBorrowTry.branch,
    AspisR1CuIterator.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual]
  rfl

theorem source_some (self : (Enum T)) (value : T) (state : (Iter T))
    (inner : (Iter T) → Option T → (Iter T))
    (hn : Aeneas.Std.core.slice.iter.IteratorIterMut.next self.iter = .ok (some value,state,inner)) :
    next self = (do
      let count ← UScalar.add self.count 1#usize
      Result.ok (some (self.count,value),({iter := state,count := count} : (Enum T)),
        someBack self value inner)) := by
  simp only [next,AspisR1CuIterator.EnumerateIterMut.Insts.CoreIterTraitsIteratorIteratorPairUsizeMutAT.next,
    hn,bind_tc_ok,AspisR1CuIterator.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
    AspisR1CuBorrowOption.core.option.OptionMutAT.Insts.Aspis_cu_borrow_optionBorrowTry.branch]
  rfl

theorem someBack_iter (self out : (Enum T)) (value replacement : T)
    (inner : (Iter T) → Option T → (Iter T)) (index : Usize) :
    (someBack self value inner out (some (index,replacement))).iter =
      inner out.iter (some replacement) := rfl

theorem someBack_count (self out : (Enum T)) (value : T)
    (inner : (Iter T) → Option T → (Iter T)) (replacement : Option (Usize × T)) :
    (someBack self value inner out replacement).count = self.count := rfl

theorem noneBack_iter (self out : (Enum T)) (inner : (Iter T) → Option T → (Iter T))
    (replacement : Option (Usize × T)) :
    (noneBack self inner out replacement).iter = inner out.iter none := rfl

#print axioms source_none
#print axioms source_some
#print axioms someBack_iter
#print axioms someBack_count
#print axioms noneBack_iter
end AspisR1.CuSavingsIteratorSource
