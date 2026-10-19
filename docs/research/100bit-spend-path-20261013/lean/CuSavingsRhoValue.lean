import CuSavingsRhoScalar

/-! Exact execution of BatchedWeights::value: a valid Vec index is read once,
all four arbitrary u64 residues are canonically reduced, and those exact words
are returned in the QM31 carrier. No canonicality of the raw array is assumed.
-/
set_option autoImplicit false
namespace AspisR1.CuSavingsRhoValue
open Aeneas Aeneas.Std Result
open AspisV8R17.RawReducer
open AspisR1CuRho

def canonicalWord (x : U64) : U32 :=
  UScalar.ofNatCore (x.val % P) (by
    have h := Nat.mod_lt x.val (show 0 < P by decide)
    change x.val % P < 4294967296
    change x.val % P < 2147483647 at h
    omega)

theorem canonicalWord_val (x : U64) : (canonicalWord x).val = x.val % P := rfl

theorem reducer_returns (x : U64) :
    field.M31.reduce_u64 x = .ok (canonicalWord x) := by
  obtain ⟨z,hr,hv,_⟩ := CuSavingsRhoScalar.reducer_mod x
  have hz : z = canonicalWord x := UScalar.eq_of_val_eq hv
  simpa only [hz] using hr

theorem mapState_reduce (xs : List U64) :
    mapState (BuiltinFnMut U64 field.M31).call_mut xs field.M31.reduce_u64 =
      .ok (xs.map canonicalWord,field.M31.reduce_u64) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [mapState,BuiltinFnMut,reducer_returns,bind_tc_ok,List.map_cons]
    change (do
      let pair ← mapState (BuiltinFnMut U64 field.M31).call_mut xs field.M31.reduce_u64
      ok (canonicalWord x::pair.1,pair.2)) = _
    rw [ih]
    rfl

def reducedArray {N : Usize} (raw : Array U64 N) : Array U32 N :=
  ⟨raw.val.map canonicalWord,by simpa only [List.length_map] using raw.property⟩

theorem array_map_reduce {N : Usize} (raw : Array U64 N) :
    AspisR1CuRho.core.array.Array.map (BuiltinFnMut U64 field.M31) raw
      field.M31.reduce_u64 = .ok (reducedArray raw) := by
  unfold AspisR1CuRho.core.array.Array.map
  split
  · rename_i ys last heq
    have hpair := Result.ok.inj (heq.symm.trans (mapState_reduce raw.val))
    cases hpair
    rfl
  · rename_i error heq
    have hbad := heq.symm.trans (mapState_reduce raw.val)
    cases hbad
  · rename_i heq
    have hbad := heq.symm.trans (mapState_reduce raw.val)
    cases hbad

def wordAt {T : Type} (raw : Array T 4#usize) (i : Fin 4) : T :=
  raw.val[i.val]'(by simpa [raw.property] using i.isLt)

theorem array_read {T : Type} (raw : Array T 4#usize) (i : Usize) (hi : i.val < 4) :
    Array.index_usize raw i = .ok (wordAt raw ⟨i.val,hi⟩) := by
  have hidx : i.val < raw.val.length := by simpa [raw.property] using hi
  unfold Array.index_usize
  change (match raw.val[i.val]? with
    | none => Result.fail Error.arrayOutOfBounds
    | some x => Result.ok x) = Result.ok (raw.val[i.val]'hidx)
  rw [List.getElem?_eq_getElem hidx]

def canonicalValue (raw : Array U64 4#usize) : field.QM31 :=
  { c0 := { a := canonicalWord (wordAt raw 0), b := canonicalWord (wordAt raw 1) }
    c1 := { a := canonicalWord (wordAt raw 2), b := canonicalWord (wordAt raw 3) } }

theorem reduced_read (raw : Array U64 4#usize) (i : Fin 4) :
    wordAt (reducedArray raw) i = canonicalWord (wordAt raw i) := by
  simp only [wordAt,reducedArray,List.getElem_map]

theorem value_from_read (self : verifier.BatchedWeights) (index : Usize)
    (raw : Array U64 4#usize)
    (hread : alloc.vec.Vec.index (Aeneas.Std.core.slice.index.SliceIndexUsizeSlice
      (Array U64 4#usize)) self.raw index = .ok raw) :
    verifier.BatchedWeights.value self index = .ok (canonicalValue raw) := by
  simp only [verifier.BatchedWeights.value,hread,array_map_reduce,bind_tc_ok,
    array_read _ 0#usize (by decide),array_read _ 1#usize (by decide),
    array_read _ 2#usize (by decide),array_read _ 3#usize (by decide),reduced_read]
  rfl

theorem value_success (self : verifier.BatchedWeights) (index : Usize)
    (hi : index.val < self.raw.val.length) :
    ∃ raw : Array U64 4#usize,
      verifier.BatchedWeights.value self index = .ok (canonicalValue raw) ∧
      raw = self.raw.val[index.val]'hi := by
  let raw := self.raw.val[index.val]'hi
  have hread : alloc.vec.Vec.index (Aeneas.Std.core.slice.index.SliceIndexUsizeSlice
      (Array U64 4#usize)) self.raw index = .ok raw := by
    unfold alloc.vec.Vec.index Aeneas.Std.core.slice.index.SliceIndexUsizeSlice
    change Slice.index_usize self.raw index = .ok raw
    unfold Slice.index_usize
    simp only [Slice.getElem?_Usize_eq,List.getElem?_eq_getElem hi]
    rfl
  exact ⟨raw,value_from_read self index raw hread,rfl⟩

#print axioms reducer_returns
#print axioms array_map_reduce
#print axioms value_from_read
#print axioms value_success
end AspisR1.CuSavingsRhoValue
