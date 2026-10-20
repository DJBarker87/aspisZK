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
    | none => .fail .arrayOutOfBounds
    | some x => .ok x) = .ok out at h
  cases hi : v.val[i.val]? with
  | none => simp [hi] at h
  | some x =>
    obtain ⟨hb,hvalue⟩ := List.getElem?_eq_some_iff.mp hi
    have he : x=out := Result.ok.inj (by simpa [hi] using h)
    exact ⟨hb,he.symm.trans hvalue.symm⟩

theorem for_query_success (g : QueryGeometry) (index : Usize) (out : Array M31 5#usize)
    (h : QueryGeometry.for_query g index = .ok out) :
    ∃ local : Usize,
      (index-g.start : Result Usize) = .ok local ∧
      g.start.val≤index.val ∧ local.val=index.val-g.start.val ∧
      g.start.val+local.val=index.val ∧
      ∃ hb : local.val<g.inverses.val.length, out=g.inverses.val[local.val]'hb := by
  unfold QueryGeometry.for_query at h
  obtain ⟨local,hsub,hread⟩ := bind_ok_inv h
  have hs := UScalar.sub_equiv index g.start
  rw [hsub] at hs
  rw [Vec.index_slice_index] at hread
  obtain ⟨hb,hout⟩ := vec_index_success g.inverses local out hread
  exact ⟨local,hsub,hs.1,by omega,by omega,hb,hout⟩

theorem entry_success_same_absolute_query (g : QueryGeometry) (index : Usize)
    (out : Array M31 5#usize) (queries : Array U32 22#usize)
    (h : for_query_entry g index = .ok out) :
    ∃ local : Usize,
      g.start.val≤index.val ∧ local.val=index.val-g.start.val ∧
      (∃ hb : local.val<g.inverses.val.length, out=g.inverses.val[local.val]'hb) ∧
      queries.val.getD (g.start.val+local.val) 0#u32 = queries.val.getD index.val 0#u32 := by
  obtain ⟨local,_,hstart,hlocal,habs,hout⟩ := for_query_success g index out h
  exact ⟨local,hstart,hlocal,hout,by rw [habs]⟩

#print axioms for_query_success
#print axioms entry_success_same_absolute_query
end AspisR1GeometryLookup.Proof
