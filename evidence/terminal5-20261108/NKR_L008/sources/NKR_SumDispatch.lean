import NKJ_Cohort
import NGA_Indexed
set_option autoImplicit false
noncomputable section
namespace NKR_SumDispatch
open Aeneas Aeneas.Std Result Error
abbrev Q := NGA_Cache.Q
abbrev Canon := NGA_Cache.Canonical
abbrev A4 := Array Q 4#usize

def selectedPrefix (n : Usize) (h : n.val≤4) (x : A4) : Array Q n :=
 ⟨x.val.take n.val,by simp only [List.length_take,x.property];exact Nat.min_eq_left h⟩

theorem canonical_prefix (n : Usize) (h : n.val≤4) (x : A4)
 (hx : ∀ q∈x.val,Canon q) : ∀ q∈(selectedPrefix n h x).val,Canon q := by
 intro q hq
 exact hx q (List.mem_of_mem_take hq)

theorem take_zip {A B : Type} (n : Nat) (xs : List A) (ys : List B) :
 (xs.take n).zip (ys.take n)=(xs.zip ys).take n := by
 induction n generalizing xs ys with
 | zero => simp
 | succ n ih =>
  cases xs <;> cases ys <;> simp [List.take,List.zip,ih]

theorem same_pairs (n : Usize) (h : n.val≤4) (l r : A4) :
 (selectedPrefix n h l).val.zip (selectedPrefix n h r).val=(l.val.zip r.val).take n.val := by
 exact take_zip n.val l.val r.val

def first (a : A4) : Q := NGA_Indexed.selected a ⟨0,by decide⟩

/-- Source-ordered frozen count dispatch. Branches2/3/4 select the SAME
selectedPrefix arrays; branch1 is emitted QM31.mul and other counts abort. -/
def reference (l r : A4) (count : Nat) : Result Q :=
 match count with
 | 1 => AspisR1SelectedMaskProbe.field.QM31.mul (first l) (first r)
 | 2 => NGA_Wrappers.sum2 (selectedPrefix 2#usize (by decide) l) (selectedPrefix 2#usize (by decide) r)
 | 3 => NGA_Wrappers.sum3 (selectedPrefix 3#usize (by decide) l) (selectedPrefix 3#usize (by decide) r)
 | 4 => NGA_Wrappers.sum4 l r
 | _ => fail panic

/-- Instantiates the CLOSED040/041/043 native computations at the parent's
actual arrays. All domains are internally derived from canonical input cells. -/
def native (l r : A4) (count : Nat) : Result Q :=
 match count with
 | 1 => AspisR1SelectedMaskProbe.field.QM31.mul (first l) (first r)
 | 2 => NKJ_NativeSmall.run ((selectedPrefix 2#usize (by decide) l).val.zip (selectedPrefix 2#usize (by decide) r).val)
 | 3 => NKJ_NativeSmall.run ((selectedPrefix 3#usize (by decide) l).val.zip (selectedPrefix 3#usize (by decide) r).val)
 | 4 => NKJ_NativeSmall.run (l.val.zip r.val)
 | _ => fail panic

theorem native_reference (l r : A4) (count : Nat)
 (hl : ∀ q∈l.val,Canon q) (hr : ∀ q∈r.val,Canon q) : native l r count=reference l r count := by
 unfold native reference
 split <;> try rfl
 · exact NKJ_Root.small _ _ (by decide) (by decide)
    (canonical_prefix _ _ l hl) (canonical_prefix _ _ r hr)
 · exact NKJ_Root.small _ _ (by decide) (by decide)
    (canonical_prefix _ _ l hl) (canonical_prefix _ _ r hr)
 · exact NKJ_Root.small l r (by decide) (by decide) hl hr

/-- The canonical array domain supplied to every helper. Its accumulator
budget is established inside NKJ_NativeSmall.source by n+remaining<=4,
not an extra parent premise. -/
theorem helper_domains (l r : A4)
 (hl : ∀ q∈l.val,Canon q) (hr : ∀ q∈r.val,Canon q) :
 ∀ (n : Usize) (h : n.val≤4),
 ((selectedPrefix n h l).val.zip (selectedPrefix n h r).val).length=n.val ∧
 ∀ p∈(selectedPrefix n h l).val.zip (selectedPrefix n h r).val,Canon p.1 ∧ Canon p.2 := by
 intro n h
 exact NGA_Wrappers.domain _ _ (canonical_prefix n h l hl) (canonical_prefix n h r hr)

#print axioms canonical_prefix
#print axioms take_zip
#print axioms same_pairs
#print axioms native_reference
#print axioms helper_domains
end NKR_SumDispatch
end
