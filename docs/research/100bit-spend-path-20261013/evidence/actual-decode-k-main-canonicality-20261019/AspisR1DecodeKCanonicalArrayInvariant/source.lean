import AspisR1DecodeKFullV10.Funs

set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisR1DecodeKCanonicalArrayInvariant

abbrev QM := AspisR1DecodeKFullV10.aspis_core.field.QM31
abbrev DecodeError := AspisR1DecodeKFullV10.r1_wire.Error
abbrev Canonical (q : QM) : Prop :=
  q.c0.a.val < AspisR1DecodeKFullV10.aspis_core.field.P.val ∧
  q.c0.b.val < AspisR1DecodeKFullV10.aspis_core.field.P.val ∧
  q.c1.a.val < AspisR1DecodeKFullV10.aspis_core.field.P.val ∧
  q.c1.b.val < AspisR1DecodeKFullV10.aspis_core.field.P.val
abbrev CanonicalArray {n : Usize} (a : Array QM n) : Prop :=
  ∀ j : Fin n, Canonical (a.val[j.val]'(by simpa [a.property] using j.isLt))

private theorem set_canonical {n : Usize} (a : Array QM n) (i : Usize) (x : QM)
    (ha : CanonicalArray a) (hx : Canonical x) : CanonicalArray (a.set i x) := by
  intro j
  have hjSet : j.val < (a.val.set i.val x).length := by simpa using j.isLt
  have hjOld : j.val < a.val.length := by simpa [a.property] using j.isLt
  change Canonical ((a.val.set i.val x)[j.val]'hjSet)
  by_cases heq : i.val = j.val
  · have hcell : (a.val.set i.val x)[j.val]'hjSet = x := by
      have hself := List.getElem_set_self (l := a.val) (i := i.val) (a := x)
        (by simpa [heq] using hjSet)
      simpa [heq] using hself
    rw [hcell]
    exact hx
  · have hcell : (a.val.set i.val x)[j.val]'hjSet = a.val[j.val]'hjOld := by
      simpa using (List.getElem_set_ne (l := a.val) (i := i.val) (j := j.val)
        heq hjSet)
    rw [hcell]
    exact ha j

theorem set_canonical_public {n : Usize} (a : Array QM n) (i : Usize) (x : QM)
    (ha : CanonicalArray a) (hx : Canonical x) : CanonicalArray (a.set i x) :=
  set_canonical a i x ha hx

theorem update_success_set {n : Usize} (a : Array QM n) (i : Usize) (x : QM)
    (hi : i.val < n.val) :
    ∃ out : Array QM n, Array.update a i x = .ok out ∧ out = a.set i x := by
  obtain ⟨out, hr, hs⟩ := WP.spec_imp_exists
    (Array.update_spec a i x (by simpa [a.property] using hi))
  exact ⟨out, hr, hs⟩

#print axioms set_canonical_public
#print axioms update_success_set
end AspisR1DecodeKCanonicalArrayInvariant
