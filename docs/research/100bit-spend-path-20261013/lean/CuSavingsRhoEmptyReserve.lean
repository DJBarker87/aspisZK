import AspisR1RhoEmptyReserve.Funs

/-! The exact safe std wrapper mutates only RawVec, never Vec.len. For its
actual empty input, length zero uniquely determines the logical Vec contents;
no preservation/copying law for allocated buffer bytes is needed. -/
set_option autoImplicit false
namespace AspisR1.CuSavingsRhoEmptyReserve
open Aeneas Aeneas.Std Result AspisR1RhoEmptyReserve

theorem source_outcome {B E : Type} (ops : RawReserve B E)
    (input : VecProjection B) (additional : Usize) :
    source_reserve ops input additional = (do
      let (result,buffer) ← ops.try_reserve_exact input.buf input.len additional
      .ok (result,{input with buf:=buffer})) := rfl

theorem source_length {B E : Type} (ops : RawReserve B E)
    (input out : VecProjection B) (additional : Usize)
    (result : core.result.Result Unit E)
    (h : source_reserve ops input additional = .ok (result,out)) :
    out.len=input.len := by
  unfold source_reserve at h
  cases hr : ops.try_reserve_exact input.buf input.len additional with
  | fail error => simp only [hr,bind_tc_fail] at h;cases h
  | div => simp only [hr,bind_tc_div] at h;cases h
  | ok pair =>
    simp only [hr,bind_tc_ok,uncurry_apply_pair] at h
    have hout := congrArg Prod.snd (Result.ok.inj h)
    exact (congrArg VecProjection.len hout).symm

theorem logical_empty_unique {T : Type} (logical : alloc.vec.Vec T)
    (h : logical.val.length=0) : logical=alloc.vec.Vec.new T := by
  apply Subtype.ext
  change logical.val=[]
  cases hv : logical.val with
  | nil => rfl
  | cons head tail => simp only [hv,List.length_cons] at h;omega

/-- Arbitrary return/error and arbitrary RawVec state cannot create a logical
value in a vector whose source length field remains zero. -/
theorem source_empty_projection {B E T : Type} (ops : RawReserve B E)
    (buffer : B) (out : VecProjection B) (additional : Usize)
    (result : core.result.Result Unit E) (logical : alloc.vec.Vec T)
    (h : source_reserve ops ⟨buffer,0#usize⟩ additional = .ok (result,out))
    (representation_length : logical.val.length=out.len.val) :
    logical=alloc.vec.Vec.new T := by
  apply logical_empty_unique
  have hl := source_length ops ⟨buffer,0#usize⟩ out additional result h
  rw [representation_length,hl]
  scalar_tac

#print axioms source_outcome
#print axioms source_length
#print axioms logical_empty_unique
#print axioms source_empty_projection
end AspisR1.CuSavingsRhoEmptyReserve
