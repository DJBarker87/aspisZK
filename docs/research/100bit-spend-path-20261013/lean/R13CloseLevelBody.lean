import R13CloseLoop
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1Stage2.R13Close.Level
abbrev Idx := Array U32 16#usize
abbrev Val := Array (Array U8 32#usize) 16#usize
abbrev Out := ControlFlow (multiproof.Arity × Idx × Val × Usize × Usize × Usize × Option Bool) (multiproof.Arity × Idx × Val × Usize × Usize × Option Bool × U32)
structure LevelOps where
  eight : Idx → Val → Usize → Usize → Usize → Option Bool → U32 → Result Out

def multiproof.index_at
  (indices : Array Std.U32 16#usize) (index : Std.Usize) : Result Std.U32 := do
  Array.index_usize indices index

def multiproof.Arity.bits (self : multiproof.Arity) : Result Std.U32 := do
  match self with
  | multiproof.Arity.Two => ok 1#u32
  | multiproof.Arity.Eight => ok 3#u32

def levelBody (ops : LevelOps)
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (hash : H) (n : Std.Usize) (nodes : Slice Std.U8) (arity : multiproof.Arity)
  (idx : Array Std.U32 16#usize) (val : Array (Array Std.U8 32#usize) 16#usize)
  (at1 : Std.Usize) (w : Std.Usize) (i : Std.Usize)
  (pending_return : Option Bool) :
  Result (ControlFlow (multiproof.Arity × (Array Std.U32 16#usize) × (Array
    (Array Std.U8 32#usize) 16#usize) × Std.Usize × Std.Usize × Std.Usize ×
    (Option Bool)) (multiproof.Arity × (Array Std.U32 16#usize) × (Array
    (Array Std.U8 32#usize) 16#usize) × Std.Usize × Std.Usize × (Option
    Bool) × Std.U32))
  := do
  if i < n
  then
    let i1 ← multiproof.index_at idx i
    let i2 ← multiproof.Arity.bits arity
    let parent ← i1 >>> i2
    match arity with
    | multiproof.Arity.Two =>
      let i3 ← i + 1#usize
      if i3 < n
      then
        let i4 ← multiproof.index_at idx i3
        let i5 ← lift (i1 ^^^ 1#u32)
        if i4 = i5
        then
          let d ←
            multiproof.occupied_binary_parent aspis_coredigestDigest32Inst hash
              val i
          let i6 ← i + 2#usize
          let idx1 ← Array.update idx w parent
          let val1 ← Array.update val w d
          let w1 ← w + 1#usize
          ok (cont (multiproof.Arity.Two, idx1, val1, at1, w1, i6,
            pending_return))
        else
          let i6 ← at1 + 32#usize
          let o ←
            core.slice.Slice.get (core.slice.index.SliceIndexRangeUsizeSlice
              Std.U8) nodes { start := at1, «end» := i6 }
          match o with
          | none =>
            ok (done (multiproof.Arity.Two, idx, val, n, at1, some false,
              0#u32))
          | some sibling =>
            let i7 ← lift (i1 &&& 1#u32)
            let d ←
              multiproof.sibling_binary_parent aspis_coredigestDigest32Inst
                hash val i sibling (i7 = 0#u32)
            let idx1 ← Array.update idx w parent
            let val1 ← Array.update val w d
            let w1 ← w + 1#usize
            ok (cont (multiproof.Arity.Two, idx1, val1, i6, w1, i3,
              pending_return))
      else
        let i4 ← at1 + 32#usize
        let o ←
          core.slice.Slice.get (core.slice.index.SliceIndexRangeUsizeSlice
            Std.U8) nodes { start := at1, «end» := i4 }
        match o with
        | none =>
          ok (done (multiproof.Arity.Two, idx, val, n, at1, some false, 0#u32))
        | some sibling =>
          let i5 ← lift (i1 &&& 1#u32)
          let d ←
            multiproof.sibling_binary_parent aspis_coredigestDigest32Inst hash
              val i sibling (i5 = 0#u32)
          let idx1 ← Array.update idx w parent
          let val1 ← Array.update val w d
          let w1 ← w + 1#usize
          ok (cont (multiproof.Arity.Two, idx1, val1, i4, w1, i3,
            pending_return))
    | multiproof.Arity.Eight => ops.eight idx val at1 w i pending_return parent
  else ok (done (arity, idx, val, w, at1, pending_return, 1#u32))

end AspisR1Stage2.R13Close.Level
