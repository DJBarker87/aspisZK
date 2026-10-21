import CurrentPowersConcreteMul
import CurrentWideMulExactProduct
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1PowersExactProduct
open AspisR1PowersConcreteMul
abbrev FullWide := AspisR1CurrentWide.Proof.E

def toFullQM (x : CallbackQM) : AspisR1CurrentWide.field.QM31 :=
  ⟨⟨x.c0.a,x.c0.b⟩,⟨x.c1.a,x.c1.b⟩⟩
def toFull (x : CallbackWide) : FullWide := ⟨toFullQM x.c0,toFullQM x.c1⟩
def fromFullQM (x : AspisR1CurrentWide.field.QM31) : CallbackQM :=
  ⟨⟨x.c0.a,x.c0.b⟩,⟨x.c1.a,x.c1.b⟩⟩
def fromFull (x : FullWide) : CallbackWide := ⟨fromFullQM x.c0,fromFullQM x.c1⟩

theorem to_from_full (x : FullWide) : toFull (fromFull x) = x := by rfl

def decode (x : CallbackWide) : AspisWideTower.WideExact :=
  AspisR1CurrentWide.Proof.decodeWide (toFull x)

theorem full_success_is_sourceMul (x y : CallbackWide) (z : FullWide)
    (h : AspisR1CurrentWide.field.wide_exact.WideExact.mul (toFull x) (toFull y) = .ok z) :
    sourceMul x y = .ok (fromFull z) := by
  have hm := AspisR1CurrentWide.Proof.wide_mul_same_minimal (toFull x) (toFull y)
  rw [h,bind_tc_ok] at hm
  have hs : AspisR1CurrentWideMul.field.wide_exact.WideExact.mul (toWide x) (toWide y) =
      .ok (AspisR1CurrentWide.Proof.toMinimalWide z) := hm.symm
  simp only [sourceMul,hs,bind_tc_ok]
  rfl

theorem sourceMul_total_exact (x y : CallbackWide) (hx : Canonical x) (hy : Canonical y) :
    ∃ z, sourceMul x y = .ok z ∧ Canonical z ∧ decode z = decode x * decode y := by
  have hx' : AspisR1CurrentWide.Proof.CanonicalWide (toFull x) := hx
  have hy' : AspisR1CurrentWide.Proof.CanonicalWide (toFull y) := hy
  obtain ⟨z,hz,hc,he⟩ := AspisR1CurrentWide.Proof.wide_mul_total_exact
    (toFull x) (toFull y) hx' hy'
  refine ⟨fromFull z,full_success_is_sourceMul x y z hz,?_,?_⟩
  · exact hc
  · simpa only [decode,to_from_full] using he

theorem sourceMul_success_exact (x y z : CallbackWide) (hx : Canonical x) (hy : Canonical y)
    (h : sourceMul x y = .ok z) : Canonical z ∧ decode z = decode x * decode y := by
  obtain ⟨out,ho,hc,he⟩ := sourceMul_total_exact x y hx hy
  have hz : out = z := Result.ok.inj (ho.symm.trans h)
  subst out
  exact ⟨hc,he⟩

theorem powers_callback_success_exact {N : Usize} (p x value : CallbackWide)
    (next : AspisR1CurrentPowers.weights.powers.closure N)
    (hp : Canonical p) (hx : Canonical x) (i : Usize)
    (h : AspisR1CurrentPowers.weights.powers.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeWideExact.call_once
      sourceMul (N := N) (p,x) i = .ok (value,next)) :
    value = p ∧ next.2 = x ∧ Canonical next.1 ∧ decode next.1 = decode p * decode x := by
  obtain ⟨product,hm,hv,hn⟩ := AspisR1CurrentPowers.call_once_success_mul sourceMul p x value next i h
  obtain ⟨hc,he⟩ := sourceMul_success_exact p x product hp hx hm
  rw [hn]
  exact ⟨hv,rfl,hc,he⟩

theorem powers_callback_total_exact {N : Usize} (p x : CallbackWide)
    (hp : Canonical p) (hx : Canonical x) (i : Usize) :
    ∃ next, Canonical next ∧ decode next = decode p * decode x ∧
      AspisR1CurrentPowers.weights.powers.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeWideExact.call_once
        sourceMul (N := N) (p,x) i = .ok (p,(next,x)) := by
  obtain ⟨next,hm,hc,he⟩ := sourceMul_total_exact p x hp hx
  exact ⟨next,hc,he,AspisR1CurrentPowers.call_once_of_mul sourceMul p x next i hm⟩

#print axioms to_from_full
#print axioms full_success_is_sourceMul
#print axioms sourceMul_total_exact
#print axioms sourceMul_success_exact
#print axioms powers_callback_success_exact
#print axioms powers_callback_total_exact
end AspisR1PowersExactProduct
