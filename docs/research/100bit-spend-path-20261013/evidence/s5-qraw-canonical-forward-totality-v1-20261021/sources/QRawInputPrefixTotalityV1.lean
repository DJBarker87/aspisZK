import AspisR1CanonicalQRawUnified.Funs
import SelectorArrayMapRuntimeSlice
import SelectorArrayMapSuccess

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CanonicalQRawUnified.Proof
open AspisV8R19.TraversalRuntime

private abbrev U32 := UScalar UScalarTy.U32
private abbrev U64 := UScalar UScalarTy.U64

private theorem mapState_zero (xs : List U32) :
    mapState AspisR1CanonicalQRawUnified.canonical.Q.raw.closure.Insts.CoreOpsFunctionFnMutTupleU32U64.call_mut
      xs () = .ok (xs.map core.convert.num.FromU64U32.from, ()) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [mapState]
      have hx : AspisR1CanonicalQRawUnified.canonical.Q.raw.closure.Insts.CoreOpsFunctionFnMutTupleU32U64.call_mut
          () x = .ok (core.convert.num.FromU64U32.from x, ()) := by
        simp [AspisR1CanonicalQRawUnified.canonical.Q.raw.closure.Insts.CoreOpsFunctionFnMutTupleU32U64.call_mut,
          core.convert.num.FromU64U32.from, lift]
      rw [hx]
      simp only [bind_tc_ok]
      rw [ih]
      rfl

private theorem mapState_one (xs : List U32) :
    mapState AspisR1CanonicalQRawUnified.canonical.Q.raw.closure_1.Insts.CoreOpsFunctionFnMutTupleU32U64.call_mut
      xs () = .ok (xs.map core.convert.num.FromU64U32.from, ()) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [mapState]
      have hx : AspisR1CanonicalQRawUnified.canonical.Q.raw.closure_1.Insts.CoreOpsFunctionFnMutTupleU32U64.call_mut
          () x = .ok (core.convert.num.FromU64U32.from x, ()) := by
        simp [AspisR1CanonicalQRawUnified.canonical.Q.raw.closure_1.Insts.CoreOpsFunctionFnMutTupleU32U64.call_mut,
          core.convert.num.FromU64U32.from, lift]
      rw [hx]
      simp only [bind_tc_ok]
      rw [ih]
      rfl

theorem raw_left_map_total (x : Array U32 4#usize) :
    ∃ mapped : Array U64 4#usize,
      core.array.Array.map
        AspisR1CanonicalQRawUnified.canonical.Q.raw.closure.Insts.CoreOpsFunctionFnMutTupleU32U64
        x () = .ok mapped := by
  have hstate := mapState_zero x.val
  have hmap := core.array.Array.map_success
    AspisR1CanonicalQRawUnified.canonical.Q.raw.closure.Insts.CoreOpsFunctionFnMutTupleU32U64
    x () (x.val.map core.convert.num.FromU64U32.from) () hstate
  exact ⟨⟨x.val.map core.convert.num.FromU64U32.from,
    (mapState_length _ _ _ _ _ hstate).trans x.property⟩, hmap⟩

theorem raw_right_map_total (x : Array U32 4#usize) :
    ∃ mapped : Array U64 4#usize,
      core.array.Array.map
        AspisR1CanonicalQRawUnified.canonical.Q.raw.closure_1.Insts.CoreOpsFunctionFnMutTupleU32U64
        x () = .ok mapped := by
  have hstate := mapState_one x.val
  have hmap := core.array.Array.map_success
    AspisR1CanonicalQRawUnified.canonical.Q.raw.closure_1.Insts.CoreOpsFunctionFnMutTupleU32U64
    x () (x.val.map core.convert.num.FromU64U32.from) () hstate
  exact ⟨⟨x.val.map core.convert.num.FromU64U32.from,
    (mapState_length _ _ _ _ _ hstate).trans x.property⟩, hmap⟩

private theorem index_usize_ok_local {α : Type} {n : Usize}
    (a : Array α n) (i : Usize) (hi : i.val < n.val) :
    Array.index_usize a i = .ok (a.val[i.val]'(by simpa [a.property] using hi)) := by
  have hidx : i.val < a.val.length := by simpa [a.property] using hi
  unfold Array.index_usize
  change (match a.val[i.val]? with
    | none => Result.fail Error.arrayOutOfBounds
    | some x => Result.ok x) = Result.ok (a.val[i.val]'hidx)
  rw [List.getElem?_eq_getElem hidx]

private theorem index_total {α : Type} (a : Array α 4#usize) (i : Usize)
    (hi : i.val < (4#usize).val) :
    ∃ x, Array.index_usize a i = .ok x := by
  have h := index_usize_ok_local a i hi
  exact ⟨a.val[i.val]'(by simpa [a.property] using hi), h⟩

/-- The initial emitted `map` and all eight fixed array reads are unconditionally
successful. This is the exact source prefix, before any multiplication or
canonical-limb assumptions are needed. -/
theorem qraw_input_prefix_total (self rhs : AspisR1CanonicalQRawUnified.canonical.Q) :
    ∃ (mappedL mappedR : Array U64 4#usize),
      core.array.Array.map
        AspisR1CanonicalQRawUnified.canonical.Q.raw.closure.Insts.CoreOpsFunctionFnMutTupleU32U64
        self () = .ok mappedL ∧
      core.array.Array.map
        AspisR1CanonicalQRawUnified.canonical.Q.raw.closure_1.Insts.CoreOpsFunctionFnMutTupleU32U64
        rhs () = .ok mappedR ∧
      (∃ a2 b2 c2 d2,
        Array.index_usize mappedL 0#usize = .ok a2 ∧
        Array.index_usize mappedL 1#usize = .ok b2 ∧
        Array.index_usize mappedL 2#usize = .ok c2 ∧
        Array.index_usize mappedL 3#usize = .ok d2) ∧
      (∃ e2 f2 g2 h2,
        Array.index_usize mappedR 0#usize = .ok e2 ∧
        Array.index_usize mappedR 1#usize = .ok f2 ∧
        Array.index_usize mappedR 2#usize = .ok g2 ∧
        Array.index_usize mappedR 3#usize = .ok h2) := by
  obtain ⟨mappedL, hL⟩ := raw_left_map_total self
  obtain ⟨mappedR, hR⟩ := raw_right_map_total rhs
  obtain ⟨a2,ha2⟩ := index_total mappedL 0#usize (by decide)
  obtain ⟨b2,hb2⟩ := index_total mappedL 1#usize (by decide)
  obtain ⟨c2,hc2⟩ := index_total mappedL 2#usize (by decide)
  obtain ⟨d2,hd2⟩ := index_total mappedL 3#usize (by decide)
  obtain ⟨e2,he2⟩ := index_total mappedR 0#usize (by decide)
  obtain ⟨f2,hf2⟩ := index_total mappedR 1#usize (by decide)
  obtain ⟨g2,hg2⟩ := index_total mappedR 2#usize (by decide)
  obtain ⟨h2,hh2⟩ := index_total mappedR 3#usize (by decide)
  exact ⟨mappedL,mappedR,hL,hR,⟨a2,b2,c2,d2,ha2,hb2,hc2,hd2⟩,
    ⟨e2,f2,g2,h2,he2,hf2,hg2,hh2⟩⟩

#print axioms raw_left_map_total
#print axioms raw_right_map_total
#print axioms qraw_input_prefix_total
end AspisR1CanonicalQRawUnified.Proof
