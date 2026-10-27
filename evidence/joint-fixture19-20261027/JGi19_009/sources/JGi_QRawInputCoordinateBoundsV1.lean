import JGi_QRawInputPrefixTotalityV1
import AspisR1CanonicalQRawUnified.Funs

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CanonicalQRawUnified.Proof
open AspisV8R19.TraversalRuntime

private abbrev U32 := UScalar UScalarTy.U32
private abbrev U64 := UScalar UScalarTy.U64

private theorem mapState_zero_local (xs : List U32) :
    AspisV8R19.TraversalRuntime.mapState canonical.Q.raw.closure.Insts.CoreOpsFunctionFnMutTupleU32U64.call_mut
      xs () = .ok (xs.map core.convert.num.FromU64U32.from, ()) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [AspisV8R19.TraversalRuntime.mapState]
      have hx : canonical.Q.raw.closure.Insts.CoreOpsFunctionFnMutTupleU32U64.call_mut
          () x = .ok (core.convert.num.FromU64U32.from x, ()) := by
        simp [canonical.Q.raw.closure.Insts.CoreOpsFunctionFnMutTupleU32U64.call_mut,
          core.convert.num.FromU64U32.from, lift]
      rw [hx]
      simp only [bind_tc_ok]
      rw [ih]
      rfl

private theorem mapState_one_local (xs : List U32) :
    AspisV8R19.TraversalRuntime.mapState canonical.Q.raw.closure_1.Insts.CoreOpsFunctionFnMutTupleU32U64.call_mut
      xs () = .ok (xs.map core.convert.num.FromU64U32.from, ()) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [AspisV8R19.TraversalRuntime.mapState]
      have hx : canonical.Q.raw.closure_1.Insts.CoreOpsFunctionFnMutTupleU32U64.call_mut
          () x = .ok (core.convert.num.FromU64U32.from x, ()) := by
        simp [canonical.Q.raw.closure_1.Insts.CoreOpsFunctionFnMutTupleU32U64.call_mut,
          core.convert.num.FromU64U32.from, lift]
      rw [hx]
      simp only [bind_tc_ok]
      rw [ih]
      rfl

private theorem coord_index_usize_ok_local {α : Type} {n : Usize}
    (a : Array α n) (i : Usize) (hi : i.val < n.val) :
    Array.index_usize a i = .ok (a.val[i.val]'(by simpa [a.property] using hi)) := by
  have hidx : i.val < a.val.length := by simpa [a.property] using hi
  unfold Array.index_usize
  change (match a.val[i.val]? with
    | none => Result.fail Error.arrayOutOfBounds
    | some x => Result.ok x) = Result.ok (a.val[i.val]'hidx)
  rw [List.getElem?_eq_getElem hidx]

private theorem from32_val (x : U32) :
    (core.convert.num.FromU64U32.from x).val = x.val := by
  change (x.bv.setWidth 64).toNat = x.bv.toNat
  exact BitVec.toNat_setWidth_of_le (by decide)

private theorem closure_zero_map_val (x : canonical.Q) (y : Array U64 4#usize)
    (h : core.array.Array.map canonical.Q.raw.closure.Insts.CoreOpsFunctionFnMutTupleU32U64
      x () = .ok y) : y.val = x.val.map core.convert.num.FromU64U32.from := by
  have hstate := mapState_zero_local x.val
  have hs := core.array.Array.map_success canonical.Q.raw.closure.Insts.CoreOpsFunctionFnMutTupleU32U64
    x () (x.val.map core.convert.num.FromU64U32.from) () hstate
  have heq : y = ⟨x.val.map core.convert.num.FromU64U32.from,
      (mapState_length _ _ _ _ _ hstate).trans x.property⟩ :=
    Result.ok.inj (h.symm.trans hs)
  exact congrArg (fun z : Array U64 4#usize => z.val) heq

private theorem closure_one_map_val (x : canonical.Q) (y : Array U64 4#usize)
    (h : core.array.Array.map canonical.Q.raw.closure_1.Insts.CoreOpsFunctionFnMutTupleU32U64
      x () = .ok y) : y.val = x.val.map core.convert.num.FromU64U32.from := by
  have hstate := mapState_one_local x.val
  have hs := core.array.Array.map_success canonical.Q.raw.closure_1.Insts.CoreOpsFunctionFnMutTupleU32U64
    x () (x.val.map core.convert.num.FromU64U32.from) () hstate
  have heq : y = ⟨x.val.map core.convert.num.FromU64U32.from,
      (mapState_length _ _ _ _ _ hstate).trans x.property⟩ :=
    Result.ok.inj (h.symm.trans hs)
  exact congrArg (fun z : Array U64 4#usize => z.val) heq

private theorem map_index_eq_local {n : Usize}
    (a : Array U32 n) (mapped : Array U64 n) (i : Usize)
    (hi : i.val < n.val) (hmap : mapped.val = a.val.map core.convert.num.FromU64U32.from)
    (x : U64) (hread : Array.index_usize mapped i = .ok x) :
    x.val = (a.val[i.val]!).val := by
  have hidx : i.val < mapped.val.length := by simpa [mapped.property] using hi
  have hspec := coord_index_usize_ok_local mapped i hi
  have hv : mapped.val[i.val]'hidx =
      core.convert.num.FromU64U32.from (a.val[i.val]'(by simpa [a.property] using hi)) := by
    simpa only [hmap, List.getElem_map]
  have hx : x = mapped.val[i.val]'hidx := Result.ok.inj (hread.symm.trans hspec)
  rw [hx, hv, from32_val]
  have hget : a.val[i.val]'(by simpa [a.property] using hi) = a.val[i.val]! := by
    rw [List.getElem!_eq_getElem?_getD]
    rw [List.getElem?_eq_getElem (by simpa [a.property] using hi)]
    rfl
  rw [hget]

/-- Source bounds on the eight exact Q inputs transport through the emitted
U32-to-U64 map and fixed index prefix. -/
theorem qraw_input_prefix_canonical_bounds
    (self rhs : canonical.Q)
    (hself0 : self.val[0]!.val ≤ 2^31-2) (hself1 : self.val[1]!.val ≤ 2^31-2)
    (hself2 : self.val[2]!.val ≤ 2^31-2) (hself3 : self.val[3]!.val ≤ 2^31-2)
    (hrhs0 : rhs.val[0]!.val ≤ 2^31-2) (hrhs1 : rhs.val[1]!.val ≤ 2^31-2)
    (hrhs2 : rhs.val[2]!.val ≤ 2^31-2) (hrhs3 : rhs.val[3]!.val ≤ 2^31-2) :
    ∃ (a b c d e f g h : U64),
      a.val ≤ 2^31-2 ∧ b.val ≤ 2^31-2 ∧ c.val ≤ 2^31-2 ∧ d.val ≤ 2^31-2 ∧
      e.val ≤ 2^31-2 ∧ f.val ≤ 2^31-2 ∧ g.val ≤ 2^31-2 ∧ h.val ≤ 2^31-2 ∧
      a.val = self.val[0]!.val ∧ b.val = self.val[1]!.val ∧
      c.val = self.val[2]!.val ∧ d.val = self.val[3]!.val ∧
      e.val = rhs.val[0]!.val ∧ f.val = rhs.val[1]!.val ∧
      g.val = rhs.val[2]!.val ∧ h.val = rhs.val[3]!.val := by
  rcases qraw_input_prefix_total self rhs with
    ⟨mappedL,mappedR,hmapL,hmapR,hleft,hright⟩
  rcases hleft with ⟨a,b,c,d,ha,hb,hc,hd⟩
  rcases hright with ⟨e,f,g,h,he,hf,hg,hh⟩
  have hmL := closure_zero_map_val self mappedL hmapL
  have hmR := closure_one_map_val rhs mappedR hmapR
  have hboundA : a.val ≤ 2^31-2 := by
    have q := map_index_eq_local self mappedL 0#usize (by decide) hmL a ha
    rw [q]
    exact hself0
  have hboundB : b.val ≤ 2^31-2 := by
    have q := map_index_eq_local self mappedL 1#usize (by decide) hmL b hb
    rw [q]
    exact hself1
  have hboundC : c.val ≤ 2^31-2 := by
    have q := map_index_eq_local self mappedL 2#usize (by decide) hmL c hc
    rw [q]
    exact hself2
  have hboundD : d.val ≤ 2^31-2 := by
    have q := map_index_eq_local self mappedL 3#usize (by decide) hmL d hd
    rw [q]
    exact hself3
  have hboundE : e.val ≤ 2^31-2 := by
    have q := map_index_eq_local rhs mappedR 0#usize (by decide) hmR e he
    rw [q]
    exact hrhs0
  have hboundF : f.val ≤ 2^31-2 := by
    have q := map_index_eq_local rhs mappedR 1#usize (by decide) hmR f hf
    rw [q]
    exact hrhs1
  have hboundG : g.val ≤ 2^31-2 := by
    have q := map_index_eq_local rhs mappedR 2#usize (by decide) hmR g hg
    rw [q]
    exact hrhs2
  have hboundH : h.val ≤ 2^31-2 := by
    have q := map_index_eq_local rhs mappedR 3#usize (by decide) hmR h hh
    rw [q]
    exact hrhs3
  exact ⟨a,b,c,d,e,f,g,h,hboundA,hboundB,hboundC,hboundD,hboundE,hboundF,hboundG,hboundH,
    (map_index_eq_local self mappedL 0#usize (by decide) hmL a ha),
    (map_index_eq_local self mappedL 1#usize (by decide) hmL b hb),
    (map_index_eq_local self mappedL 2#usize (by decide) hmL c hc),
    (map_index_eq_local self mappedL 3#usize (by decide) hmL d hd),
    (map_index_eq_local rhs mappedR 0#usize (by decide) hmR e he),
    (map_index_eq_local rhs mappedR 1#usize (by decide) hmR f hf),
    (map_index_eq_local rhs mappedR 2#usize (by decide) hmR g hg),
    (map_index_eq_local rhs mappedR 3#usize (by decide) hmR h hh)⟩

#print axioms qraw_input_prefix_canonical_bounds
end AspisR1CanonicalQRawUnified.Proof
