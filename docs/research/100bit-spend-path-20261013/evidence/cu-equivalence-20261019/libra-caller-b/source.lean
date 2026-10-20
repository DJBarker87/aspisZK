import CuSavingsLibraLow
import CuSavingsCanonicalInputPowers
set_option autoImplicit false
namespace AspisR1.CuSavingsLibraCaller
open Aeneas Aeneas.Std Result
open CuSavingsLibraSourceControl CuSavingsLibraConcrete
abbrev Points := Array L.E 4#usize
abbrev Low := Array L.E 16#usize

def castArray {T U : Type} {N : Usize} (f : T → U) (xs : Array T N) : Array U N :=
  ⟨xs.val.map f,by simp only [List.length_map,xs.property]⟩

theorem lookup_cast {T U : Type} {N : Usize} (f : T → U) (xs : Array T N)
    (t : T) (u : U) (i : Nat) (hi : i<N.val) :
    lookup (castArray f xs) u i=f (lookup xs t i) := by
  have hlen : i<xs.val.length := by rw [xs.property];exact hi
  change (xs.val.map f).getD i u=f (xs.val.getD i t)
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using hlen),
    List.getD_eq_getElem xs.val t hlen,List.getElem_map]

def toLow (e : L.E) : AspisR1LibraLow.field.wide_exact.WideExact := AspisR1LibraLow.fromE (toE e)
def fromLow (e : AspisR1LibraLow.field.wide_exact.WideExact) : L.E := fromE (AspisR1LibraLow.toE e)

def lowCaller (p q : Points) : Result Low := do
  let out ← AspisR1LibraLow.low (castArray toLow p) (castArray toLow q)
  .ok (castArray fromLow out)

def lowTerm (p q : Points) (i : Nat) : CuSavingsWideArithmetic.ExactE :=
  decodeEL (lookup p AspisR1Libra.field.wide_exact.WideExact.ZERO (CuSavingsLibraSourcePerm.perm (i%4))) *
  decodeEL (lookup q AspisR1Libra.field.wide_exact.WideExact.ZERO (CuSavingsLibraSourcePerm.perm (i/4))) * quarter^2

theorem perm_bound (i : Nat) (hi : i<4) : CuSavingsLibraSourcePerm.perm i<4 := by
  have hc : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
  rcases hc with h|h|h|h <;> simp [CuSavingsLibraSourcePerm.perm,h]

theorem low_success (p q : Points)
    (hp : ∀ i,i<4 → canonicalE (lookup p AspisR1Libra.field.wide_exact.WideExact.ZERO i))
    (hq : ∀ i,i<4 → canonicalE (lookup q AspisR1Libra.field.wide_exact.WideExact.ZERO i)) :
    ∃ out,lowCaller p q=.ok out ∧ ∀ i,i<16 →
      canonicalE (lookup out AspisR1Libra.field.wide_exact.WideExact.ZERO i) ∧
      decodeEL (lookup out AspisR1Libra.field.wide_exact.WideExact.ZERO i)=lowTerm p q i := by
  have c0 : ∀ i,i<4 → CuSavingsLibraLow.canonical (lookup (castArray toLow p) CuSavingsLibraLow.zero i) := by
    intro i hi
    rw [lookup_cast toLow p AspisR1Libra.field.wide_exact.WideExact.ZERO CuSavingsLibraLow.zero i (by scalar_tac)]
    exact hp i hi
  have c1 : ∀ i,i<4 → CuSavingsLibraLow.canonical (lookup (castArray toLow q) CuSavingsLibraLow.zero i) := by
    intro i hi
    rw [lookup_cast toLow q AspisR1Libra.field.wide_exact.WideExact.ZERO CuSavingsLibraLow.zero i (by scalar_tac)]
    exact hq i hi
  obtain ⟨out,hout,hvalues⟩ := CuSavingsLibraLow.source_success (castArray toLow p) (castArray toLow q) c0 c1
  refine ⟨castArray fromLow out,?_,?_⟩
  · simp only [lowCaller,hout,bind_tc_ok]
  · intro i hi
    rw [lookup_cast fromLow out CuSavingsLibraLow.zero AspisR1Libra.field.wide_exact.WideExact.ZERO i (by scalar_tac)]
    obtain ⟨hc,hv⟩ := hvalues i hi
    refine ⟨hc,?_⟩
    change CuSavingsLibraLow.decode (lookup out CuSavingsLibraLow.zero i)=lowTerm p q i
    rw [hv]
    unfold CuSavingsLibraLow.term lowTerm
    rw [lookup_cast toLow p AspisR1Libra.field.wide_exact.WideExact.ZERO CuSavingsLibraLow.zero _ (by apply perm_bound;omega),
      lookup_cast toLow q AspisR1Libra.field.wide_exact.WideExact.ZERO CuSavingsLibraLow.zero _ (by apply perm_bound;omega),
      CuSavingsLibraLow.scale_eq_quarter_squared]
    rfl

#print axioms lookup_cast
#print axioms low_success
end AspisR1.CuSavingsLibraCaller
