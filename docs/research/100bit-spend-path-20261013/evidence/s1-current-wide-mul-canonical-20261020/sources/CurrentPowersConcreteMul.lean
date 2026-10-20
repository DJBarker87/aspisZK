import CurrentPowersCallback
import CurrentWideMulCanonical
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1PowersConcreteMul
abbrev CallbackWide := AspisR1CurrentPowers.field.WideExact
abbrev CallbackQM := AspisR1CurrentPowers.field.QM31
abbrev SourceWide := AspisR1CurrentWideMul.field.wide_exact.WideExact
abbrev SourceQM := AspisR1CurrentWideMul.field.QM31

def toQM (x : CallbackQM) : SourceQM :=
  ⟨⟨x.c0.a,x.c0.b⟩,⟨x.c1.a,x.c1.b⟩⟩
def fromQM (x : SourceQM) : CallbackQM :=
  ⟨⟨x.c0.a,x.c0.b⟩,⟨x.c1.a,x.c1.b⟩⟩
def toWide (x : CallbackWide) : SourceWide := ⟨toQM x.c0,toQM x.c1⟩
def fromWide (x : SourceWide) : CallbackWide := ⟨fromQM x.c0,fromQM x.c1⟩

theorem to_from (x : SourceWide) : toWide (fromWide x) = x := by rfl
theorem from_to (x : CallbackWide) : fromWide (toWide x) = x := by rfl

def Canonical (x : CallbackWide) : Prop := AspisR1CurrentWideMul.CanonicalWide (toWide x)

def sourceMul (x y : CallbackWide) : Result CallbackWide := do
  let z ← AspisR1CurrentWideMul.field.wide_exact.WideExact.mul (toWide x) (toWide y)
  ok (fromWide z)

theorem sourceMul_total_canonical (x y : CallbackWide) (hx : Canonical x) (hy : Canonical y) :
    ∃ z, sourceMul x y = .ok z ∧ Canonical z := by
  obtain ⟨z, hz, cz⟩ := AspisR1CurrentWideMul.wide_mul_total_canonical
    (toWide x) (toWide y) hx hy
  refine ⟨fromWide z, ?_, ?_⟩
  · simp only [sourceMul, hz, bind_tc_ok]
  · simpa only [Canonical, to_from] using cz

theorem powers_callback_total_canonical {N : Usize} (p x : CallbackWide)
    (hp : Canonical p) (hx : Canonical x) (i : Usize) :
    ∃ next, Canonical next ∧
      AspisR1CurrentPowers.weights.powers.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeWideExact.call_once
        sourceMul (N := N) (p,x) i = .ok (p,(next,x)) := by
  obtain ⟨next, hm, hc⟩ := sourceMul_total_canonical p x hp hx
  exact ⟨next,hc,AspisR1CurrentPowers.call_once_of_mul sourceMul p x next i hm⟩

theorem powers_callback_success_canonical {N : Usize} (p x value : CallbackWide)
    (next : AspisR1CurrentPowers.weights.powers.closure N)
    (hp : Canonical p) (hx : Canonical x) (i : Usize)
    (h : AspisR1CurrentPowers.weights.powers.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeWideExact.call_once
      sourceMul (N := N) (p,x) i = .ok (value,next)) :
    value = p ∧ next.2 = x ∧ Canonical next.1 := by
  obtain ⟨product, hm, hv, hn⟩ := AspisR1CurrentPowers.call_once_success_mul
    sourceMul p x value next i h
  obtain ⟨z, hz, cz⟩ := sourceMul_total_canonical p x hp hx
  have he : product = z := Result.ok.inj (hm.symm.trans hz)
  subst product
  rw [hn]
  exact ⟨hv,rfl,cz⟩

#print axioms to_from
#print axioms from_to
#print axioms sourceMul_total_canonical
#print axioms powers_callback_total_canonical
#print axioms powers_callback_success_canonical
end AspisR1PowersConcreteMul
