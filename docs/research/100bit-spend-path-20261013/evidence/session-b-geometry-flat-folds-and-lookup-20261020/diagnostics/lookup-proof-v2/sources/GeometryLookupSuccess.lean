import AspisR1GeometryLookup.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1GeometryLookup.Proof
open alloc.vec
private theorem bind_ok_inv {A B : Type} {r : Result A} {f : A → Result B} {out : B}
    (h : Bind.bind r f = .ok out) : ∃ a, r = .ok a ∧ f a = .ok out := by
  cases r with
  | ok a => exact ⟨a,rfl,h⟩
  | fail e => simp [Bind.bind] at h
  | div => simp [Bind.bind] at h

private theorem vec_index_success {A : Type} (v : Vec A) (i : Usize) (out : A)
    (h : Vec.index_usize v i = .ok out) :
    ∃ hb : i.val<v.val.length, out=v.val[i.val]'hb := by
  change (match v.val[i.val]? with
    | none => Result.fail Error.arrayOutOfBounds
    | some x => Result.ok x) = Result.ok out at h
  cases hi : v.val[i.val]? with
  | none => simp [hi] at h
  | some x =>
    obtain ⟨hb,hvalue⟩ := List.getElem?_eq_some_iff.mp hi
    have he : x=out := Result.ok.inj (by simpa [hi] using h)
    exact ⟨hb,he.symm.trans hvalue.symm⟩

theorem for_query_success (g : QueryGeometry) (index : Usize) (out : Array M31 5#usize)
    (h : QueryGeometry.for_query g index = .ok out) :
    ∃ offset : Usize,
      (index-g.start : Result Usize) = .ok offset ∧
      g.start.val≤index.val ∧ offset.val=index.val-g.start.val ∧
      g.start.val+offset.val=index.val ∧
      ∃ hb : offset.val<g.inverses.val.length, out=g.inverses.val[offset.val]'hb := by
  unfold QueryGeometry.for_query at h
  obtain ⟨offset,hsub,hread⟩ := bind_ok_inv h
  have hs := UScalar.sub_equiv index g.start
  rw [hsub] at hs
  rw [Vec.index_slice_index] at hread
  obtain ⟨hb,hout⟩ := vec_index_success g.inverses offset out hread
  exact ⟨offset,hsub,hs.1,by omega,by omega,hb,hout⟩

theorem entry_success_same_absolute_query (g : QueryGeometry) (index : Usize)
    (out : Array M31 5#usize) (queries : Array U32 22#usize)
    (h : for_query_entry g index = .ok out) :
    ∃ offset : Usize,
      g.start.val≤index.val ∧ offset.val=index.val-g.start.val ∧
      (∃ hb : offset.val<g.inverses.val.length, out=g.inverses.val[offset.val]'hb) ∧
      queries.val.getD (g.start.val+offset.val) 0#u32 = queries.val.getD index.val 0#u32 := by
  obtain ⟨offset,_,hstart,hlocal,habs,hout⟩ := for_query_success g index out h
  exact ⟨offset,hstart,hlocal,hout,by rw [habs]⟩

#print axioms for_query_success
#print axioms entry_success_same_absolute_query
end AspisR1GeometryLookup.Proof
