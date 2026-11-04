import Aeneas.Std
import Aeneas.Tactic.RustAttributes

/-! Standard-library adapters for the five unsupported bank externals.
The array adapter calls a mutable closure in increasing index order and
threads its state. Map.next calls the underlying iterator once and only
calls the closure on Some. Range membership short-circuits its comparisons.
These are definitions with kernel-checked specifications, not postulates. -/
set_option autoImplicit false
namespace R1Z.BuilderStdModels
open Aeneas Aeneas.Std Result

variable {T C I A B : Type}

def fromFnLoop (f : core.ops.function.FnMut C Std.Usize T) :
    List Std.Usize → C → Result (List T × C)
  | [], c => ok ([], c)
  | i :: is, c => do
      let (x, c') ← f.call_mut c i
      let (xs, c'') ← fromFnLoop f is c'
      ok (x :: xs, c'')

def indices (n : Std.Usize) : List Std.Usize :=
  List.ofFn (fun i : Fin n.val => Std.Usize.ofNatCore i.val
    (lt_trans i.isLt n.hBounds))

def fromFn (n : Std.Usize) (f : core.ops.function.FnMut C Std.Usize T)
    (c : C) : Result (Aeneas.Std.Array T n) := do
  let (xs, _) ← fromFnLoop f (indices n) c
  if h : xs.length = n.val then ok ⟨xs, h⟩ else .fail .panic

def iterMap (_it : core.iter.traits.iterator.Iterator I A)
    (_f : core.ops.function.FnMut C A B) (i : I) (c : C) :
    Result (core.iter.adapters.map.Map I C) := ok ⟨i, c⟩

def mapNext (it : core.iter.traits.iterator.Iterator I A)
    (f : core.ops.function.FnMut C A B) (m : core.iter.adapters.map.Map I C) :
    Result (Option B × core.iter.adapters.map.Map I C) := do
  let (x, i') ← it.next m.iter
  match x with
  | none => ok (none, ⟨i', m.f⟩)
  | some x => do
      let (y, c') ← f.call_mut m.f x
      ok (some y, ⟨i', c'⟩)

def rangeContains {Idx U : Type}
    (_ord : core.cmp.PartialOrd Idx Idx)
    (lo : core.cmp.PartialOrd Idx U) (hi : core.cmp.PartialOrd U Idx)
    (r : core.ops.range.Range Idx) (x : U) : Result Bool := do
  let b ← lo.le r.start x
  if b then hi.lt x r.end else ok false

def rangeInclusiveContains {Idx U : Type}
    (_ord : core.cmp.PartialOrd Idx Idx)
    (lo : core.cmp.PartialOrd Idx U) (hi : core.cmp.PartialOrd U Idx)
    (r : core.ops.range.RangeInclusive Idx) (x : U) : Result Bool := do
  let b ← lo.le r.start x
  if b then
    if r.exhausted then hi.lt x r.end else hi.le x r.end
  else ok false

/-- The closure's output state is passed to the next index, in order. -/
theorem fromFnLoop_cons (f : core.ops.function.FnMut C Std.Usize T)
    (i : Std.Usize) (is : List Std.Usize) (c c' c'' : C) (x : T) (xs : List T)
    (hcall : f.call_mut c i = ok (x, c'))
    (htail : fromFnLoop f is c' = ok (xs, c'')) :
    fromFnLoop f (i :: is) c = ok (x :: xs, c'') := by
  simp [fromFnLoop, hcall, htail]

theorem fromFnLoop_pure (f : core.ops.function.FnMut C Std.Usize T)
    (g : Std.Usize → T) (h : ∀ c i, f.call_mut c i = ok (g i, c))
    (is : List Std.Usize) (c : C) :
    fromFnLoop f is c = ok (is.map g, c) := by
  induction is with
  | nil => rfl
  | cons i is ih => simp [fromFnLoop, h, ih]

theorem fromFn_pure (n : Std.Usize) (f : core.ops.function.FnMut C Std.Usize T)
    (g : Std.Usize → T) (h : ∀ c i, f.call_mut c i = ok (g i, c)) (c : C) :
    fromFn n f c = ok (Aeneas.Std.Array.make n
      ((indices n).map g) (by simp [indices])) := by
  simp [fromFn, fromFnLoop_pure f g h, indices, Aeneas.Std.Array.make]

theorem iterMap_spec (it : core.iter.traits.iterator.Iterator I A)
    (f : core.ops.function.FnMut C A B) (i : I) (c : C) :
    iterMap it f i c = ok ⟨i, c⟩ := rfl

theorem mapNext_none (it : core.iter.traits.iterator.Iterator I A)
    (f : core.ops.function.FnMut C A B) (m : core.iter.adapters.map.Map I C) (i' : I)
    (h : it.next m.iter = ok (none, i')) :
    mapNext it f m = ok (none, ⟨i', m.f⟩) := by simp [mapNext, h]

theorem mapNext_some (it : core.iter.traits.iterator.Iterator I A)
    (f : core.ops.function.FnMut C A B) (m : core.iter.adapters.map.Map I C)
    (i' : I) (x : A) (y : B) (c' : C)
    (hi : it.next m.iter = ok (some x, i'))
    (hf : f.call_mut m.f x = ok (y, c')) :
    mapNext it f m = ok (some y, ⟨i', c'⟩) := by simp [mapNext, hi, hf]

theorem rangeContains_spec {Idx U : Type}
    (ord : core.cmp.PartialOrd Idx Idx)
    (lo : core.cmp.PartialOrd Idx U) (hi : core.cmp.PartialOrd U Idx)
    (r : core.ops.range.Range Idx) (x : U) (a b : Bool)
    (hl : lo.le r.start x = ok a) (hh : hi.lt x r.end = ok b) :
    rangeContains ord lo hi r x = ok (a && b) := by
  cases a <;> simp [rangeContains, hl, hh]

theorem rangeInclusiveContains_spec {Idx U : Type}
    (ord : core.cmp.PartialOrd Idx Idx)
    (lo : core.cmp.PartialOrd Idx U) (hi : core.cmp.PartialOrd U Idx)
    (r : core.ops.range.RangeInclusive Idx) (x : U) (a b : Bool)
    (he : r.exhausted = false)
    (hl : lo.le r.start x = ok a) (hh : hi.le x r.end = ok b) :
    rangeInclusiveContains ord lo hi r x = ok (a && b) := by
  cases a <;> simp [rangeInclusiveContains, he, hl, hh]

theorem rangeInclusiveContains_exhausted {Idx U : Type}
    (ord : core.cmp.PartialOrd Idx Idx)
    (lo : core.cmp.PartialOrd Idx U) (hi : core.cmp.PartialOrd U Idx)
    (r : core.ops.range.RangeInclusive Idx) (x : U) (a b : Bool)
    (he : r.exhausted = true)
    (hl : lo.le r.start x = ok a) (hh : hi.lt x r.end = ok b) :
    rangeInclusiveContains ord lo hi r x = ok (a && b) := by
  cases a <;> simp [rangeInclusiveContains, he, hl, hh]

#print axioms rangeInclusiveContains_exhausted
#print axioms fromFnLoop_cons
#print axioms fromFnLoop_pure
#print axioms fromFn_pure
#print axioms iterMap_spec
#print axioms mapNext_none
#print axioms mapNext_some
#print axioms rangeContains_spec
#print axioms rangeInclusiveContains_spec
end R1Z.BuilderStdModels
