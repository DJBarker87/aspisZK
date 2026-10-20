import CanonicalDotReduceSemantics
import SelectorArrayMapSuccess
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CanonicalDotFinish.Proof
open AspisV8R17.RawReducer

def canonicalWord (x : U64) : U32 :=
  UScalar.ofNatCore (x.val%P) (by
    have hm := Nat.mod_lt x.val (show 0<P by decide)
    have hp : P<2^32 := by decide
    exact Nat.lt_trans hm hp)

theorem canonicalWord_val (x : U64) : (canonicalWord x).val=x.val%P := rfl

theorem canonical_reduce_total (x : U64) : canonical.reduce x = .ok (canonicalWord x) := by
  obtain ⟨out,hout,hval,_⟩ := canonical_reduce_mod x
  have he : out=canonicalWord x := UScalar.eq_of_val_eq hval
  rw [←he]
  exact hout

private theorem mapState_reduce (xs : List U64) :
    AspisV8R19.TraversalRuntime.mapState (BuiltinFnMut U64 U32).call_mut
      xs canonical.reduce = .ok (xs.map canonicalWord,canonical.reduce) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      have hcall : (BuiltinFnMut U64 U32).call_mut canonical.reduce x =
          .ok (canonicalWord x,canonical.reduce) := by
        simp only [BuiltinFnMut,canonical_reduce_total]
      rw [AspisV8R19.TraversalRuntime.mapState,hcall,bind_tc_ok]
      change (do
        let pair ← AspisV8R19.TraversalRuntime.mapState (BuiltinFnMut U64 U32).call_mut xs canonical.reduce
        ok (canonicalWord x::pair.1,pair.2)) = _
      rw [ih]
      rfl

theorem canonical_dot_finish_total (dot : canonical.Dot) :
    ∃ out : canonical.Q, canonical.Dot.finish dot = .ok out ∧
      out.val = dot.sums.val.map canonicalWord ∧
      ∀ j, ∀ hj : j<4,
        (out.val[j]'(by rw [out.property];exact hj)).val =
          (dot.sums.val[j]'(by rw [dot.sums.property];exact hj)).val%P ∧
        (out.val[j]'(by rw [out.property];exact hj)).val<P := by
  let out : Array U32 4#usize := ⟨dot.sums.val.map canonicalWord,by simpa using dot.sums.property⟩
  have hstate := mapState_reduce dot.sums.val
  have hmap := Aeneas.Std.core.array.Array.map_success (BuiltinFnMut U64 U32)
    dot.sums canonical.reduce (dot.sums.val.map canonicalWord) canonical.reduce hstate
  have hfinish : canonical.Dot.finish dot = .ok out := by
    unfold canonical.Dot.finish
    rw [hmap]
    rfl
  refine ⟨out,hfinish,rfl,?_⟩
  intro j hj
  have hv : (out.val[j]'(by rw [out.property];exact hj)).val =
      (dot.sums.val[j]'(by rw [dot.sums.property];exact hj)).val%P := by
    change ((dot.sums.val.map canonicalWord)[j]'_).val = _
    rw [List.getElem_map,canonicalWord_val]
  exact ⟨hv,by rw [hv];exact Nat.mod_lt _ (by decide)⟩

theorem canonical_dot_finish_entry (sums : Array U64 4#usize) :
    ∃ out : Array U32 4#usize, finish_entry sums = .ok out ∧
      out.val=sums.val.map canonicalWord := by
  obtain ⟨out,hout,hvalues,_⟩ := canonical_dot_finish_total {sums}
  refine ⟨out,?_,hvalues⟩
  unfold finish_entry canonical.finish_entry
  rw [hout]
  rfl

#print axioms canonicalWord_val
#print axioms canonical_reduce_total
#print axioms canonical_dot_finish_total
#print axioms canonical_dot_finish_entry
end AspisR1CanonicalDotFinish.Proof
