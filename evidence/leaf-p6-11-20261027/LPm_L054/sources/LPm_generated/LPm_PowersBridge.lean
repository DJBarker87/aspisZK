import LPi_PowersSource
import LPm_StubBounds
set_option autoImplicit false
namespace AspisR1.LPm_PowersBridge
open Aeneas Aeneas.Std Result LPi_FieldValues LPi_PowersPrefix

/-- The complete eight-word carrier is fixed by its natural value port. -/
theorem values_injective (x y : NE) (same : ew x=ew y) : x=y := by
  rcases x with ⟨⟨⟨a,b⟩,⟨c,d⟩⟩,⟨⟨e,f⟩,⟨g,h⟩⟩⟩
  rcases y with ⟨⟨⟨i,j⟩,⟨k,l⟩⟩,⟨⟨m,n⟩,⟨o,p⟩⟩⟩
  simp only [ew,qw,cw,Prod.mk.injEq] at same
  rcases same with ⟨⟨⟨ha,hb⟩,⟨hc,hd⟩⟩,⟨⟨he,hf⟩,⟨hg,hh⟩⟩⟩
  simp only [UScalar.eq_of_val_eq ha,UScalar.eq_of_val_eq hb,UScalar.eq_of_val_eq hc,
    UScalar.eq_of_val_eq hd,UScalar.eq_of_val_eq he,UScalar.eq_of_val_eq hf,
    UScalar.eq_of_val_eq hg,UScalar.eq_of_val_eq hh]

/-- N source writes, but only N-1 continuing calls: the actual last branch
returns immediately. The native write/frame, continuing return and field-value
gates supply the local transitions, not a whole powers equality. -/
inductive Trace (x : NE) : Nat → NE → List NE → Prop where
  | zero (p : NE) : Trace x 0 p []
  | last (p : NE) (canonical : canonE p) : Trace x 1 p [p]
  | next {n : Nat} {p p' : NE} {xs : List NE}
      (canonical : canonE p) (value : ew p'=mulE (ew p) (ew x))
      (tail : Trace x (n+1) p' xs) : Trace x (n+2) p (p::xs)

theorem trace_values {x p : NE} {n : Nat} {xs : List NE}
    (tr : Trace x n p xs) (i : Nat) (initial : ew p=power (ew x) i) :
    ∀ j, j<n → ∃ z, xs[j]?=some z ∧ canonE z ∧ ew z=power (ew x) (i+j) := by
  induction tr generalizing i with
  | zero p => intro j hj; omega
  | last p canonical =>
    intro j hj
    have hj0 : j=0 := by omega
    subst j
    exact ⟨p,rfl,canonical,by simpa only [Nat.add_zero] using initial⟩
  | @next n p p' xs canonical value tail ih =>
    have nextValue : ew p'=power (ew x) (i+1) := by
      rw [value,initial]
      rfl
    intro j hj
    cases j with
    | zero => exact ⟨p,rfl,canonical,by simpa only [Nat.add_zero] using initial⟩
    | succ j =>
      obtain ⟨z,hz,hc,hv⟩ := ih (i+1) nextValue j (by omega)
      exact ⟨z,hz,hc,by simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hv⟩

/-- Actual seven-element returned carrier, with every word identified with
the emitted helper's Result. No independently chosen whole-output equality. -/
theorem native_result (x : NE) (canonical : canonE x) (out : Array NE 7#usize)
    (tr : Trace x 7 FIo_Native.aspis_core.field.wide_exact.WideExact.ONE out.val) :
    FIo_Native.weights.powers 7#usize x=ok out := by
  obtain ⟨model,call,holds⟩ := LPi_PowersSource.seven x canonical
  have native := trace_values tr 0 rfl
  have same : model=out := by
    apply Subtype.ext
    apply List.ext_getElem
    · exact model.property.trans out.property.symm
    · intro i hi hj
      have bound : i<7 := by
        have hlen : model.val.length=7 := model.property
        omega
      obtain ⟨z,hz,_,vz⟩ := holds i bound
      obtain ⟨w,hw,_,vw⟩ := native i bound
      rw [List.getElem?_eq_getElem hi] at hz
      rw [List.getElem?_eq_getElem hj] at hw
      rw [Option.some.inj hz,Option.some.inj hw]
      exact values_injective z w (vz.trans (by simpa only [Nat.zero_add] using vw.symm))
  rw [same] at call
  exact call

#print axioms values_injective
#print axioms trace_values
#print axioms native_result
end AspisR1.LPm_PowersBridge
