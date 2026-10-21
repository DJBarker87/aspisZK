import S7Kani2PrefixLoop
set_option autoImplicit false
namespace S7Kani3InverseLoop
open Aeneas Aeneas.Std Result
open S7Kani2PrefixLoop (wordMul multiply_word)

def inverse_owned
  (flat : alloc.vec.Vec U32)
  (prefixes : alloc.vec.Vec U32)
  (inverse : alloc.vec.Vec U32)
  (suffix : U32) (index : Std.Usize) :
  Result (alloc.vec.Vec U32)
  := do
  if index = 0#usize
  then ok inverse
  else
    let i ← index - 1#usize
    let m ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        U32) prefixes i
    let m1 ← AspisR1Qm31ArithmeticProbe.field.M31.mul suffix m
    let (_, index_mut_back) ←
      alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice
        U32) inverse i
    let inverse1 := index_mut_back m1
    let m2 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        U32) flat i
    let suffix1 ← AspisR1Qm31ArithmeticProbe.field.M31.mul suffix m2
    inverse_owned flat prefixes inverse1 suffix1 i
partial_fixpoint


def model (flat prefixes : List U32) : Nat → List U32 → U32 → List U32
 | 0,inverse,_ => inverse
 | n+1,inverse,suffix =>
     model flat prefixes n (inverse.set n (wordMul suffix (prefixes[n]?.getD 0#u32)))
       (wordMul suffix (flat[n]?.getD 0#u32))

/-- Entire emitted backward driver, with the concrete frozen multiply and
mutable Vec setter. No per-step success or equality law is a premise. -/
theorem inverse_refines (flat prefixes inverse : alloc.vec.Vec U32)
    (suffix : U32) (index : Usize)
    (bound : index.val ≤ 110)
    (hf : index.val ≤ flat.val.length) (hp : index.val ≤ prefixes.val.length)
    (hi : index.val ≤ inverse.val.length) :
    ∃ out, inverse_owned flat prefixes inverse suffix index=ok out ∧
      out.val=model flat.val prefixes.val index.val inverse.val suffix ∧
      out.val.length=inverse.val.length := by
  generalize hn : index.val=n at *
  induction n generalizing index inverse suffix with
  | zero =>
      have hz : index=0#usize := UScalar.eq_of_val_eq hn
      subst index
      refine ⟨inverse,?_,rfl,rfl⟩
      rw [inverse_owned]
      simp
  | succ n ih =>
      have hnz : index≠0#usize := by intro h; subst index; simp at hn
      obtain ⟨i,hsub,hival⟩ := AspisR1.ExtractedCurrentReducerOps.sub_success index 1#usize (by scalar_tac)
      have hisub : (index-1#usize : Result Usize)=ok i := hsub
      change i.val=index.val-1 at hival
      have hiv : i.val=n := by omega
      obtain ⟨pref,hpr,hpv⟩ := WP.spec_imp_exists
        (alloc.vec.Vec.index_usize_spec prefixes i (by change i.val < prefixes.val.length; omega))
      have hpr' : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U32) prefixes i=ok pref := hpr
      obtain ⟨x,hxr,hxv⟩ := WP.spec_imp_exists
        (alloc.vec.Vec.index_usize_spec flat i (by change i.val < flat.val.length; omega))
      have hxr' : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U32) flat i=ok x := hxr
      obtain ⟨⟨old,back⟩,hmut,_,hback⟩ := WP.spec_imp_exists
        (alloc.vec.Vec.index_mut_usize_spec inverse i (by change i.val < inverse.val.length; omega))
      have hm : alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice U32) inverse i=ok (old,back) := by
        rw [alloc.vec.Vec.index_mut_slice_index]; exact hmut
      have hslen : (inverse.set i (wordMul suffix pref)).val.length=inverse.val.length := by simp
      obtain ⟨out,hrun,hout,hlen⟩ := ih (inverse.set i (wordMul suffix pref))
        (wordMul suffix x) i hiv (by omega) (by omega) (by omega) (by omega)
      refine ⟨out,?_,?_,hlen.trans hslen⟩
      · rw [inverse_owned]
        simp only [hnz,if_false,hisub,hpr',multiply_word,hm,hback,hxr',bind_tc_ok]
        exact hrun
      · rw [hout,model]
        have hpp : prefixes.val[n]?.getD 0#u32=pref := by
          rw [List.getElem?_eq_getElem (by omega)]
          simp only [Option.getD_some]
          simpa only [hiv] using hpv.symm
        have hxx : flat.val[n]?.getD 0#u32=x := by
          rw [List.getElem?_eq_getElem (by omega)]
          simp only [Option.getD_some]
          simpa only [hiv] using hxv.symm
        simp only [hpp,hxx]
        congr 1
        change inverse.val.set i.val _=inverse.val.set n _
        rw [hiv]

#print axioms inverse_refines
end S7Kani3InverseLoop
