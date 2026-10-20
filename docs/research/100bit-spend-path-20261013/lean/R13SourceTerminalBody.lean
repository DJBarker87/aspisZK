import R13WireToBin
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1Stage2.R13SourceTerminal
open AspisR1Stage2
abbrev Indices := Array U32 16#usize
abbrev Values := Array (Array U8 32#usize) 16#usize
/-- Only the inner level loop is parameterized. It is NOT assumed correct. -/
structure TerminalOps where
  level : multiproof.Arity → Indices → Values → Usize → Slice U8 → Usize → Usize → Usize → Option Bool →
    Result (multiproof.Arity × Indices × Values × Usize × Usize × Option Bool × U32)
def multiproof.root_matches
  (values : Array (Array Std.U8 32#usize) 16#usize)
  (root : Array Std.U8 32#usize) :
  Result Bool
  := do
  let a ← Array.index_usize values 0#usize
  core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 a root
def multiproof.index_at
  (indices : Array Std.U32 16#usize) (index : Std.Usize) : Result Std.U32 := do
  Array.index_usize indices index

def terminalBody
  (ops : TerminalOps)
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (hash : H) (root : Array Std.U8 32#usize) (nodes : Slice Std.U8)
  (iter : core.ops.range.Range Std.U32) (arity : multiproof.Arity)
  (idx : Array Std.U32 16#usize) (val : Array (Array Std.U8 32#usize) 16#usize)
  (n : Std.Usize) (at1 : Std.Usize) (pending_return : Option Bool) :
  Result (ControlFlow ((core.ops.range.Range Std.U32) × multiproof.Arity ×
    (Array Std.U32 16#usize) × (Array (Array Std.U8 32#usize) 16#usize) ×
    Std.Usize × Std.Usize × (Option Bool)) ((Array Std.U32 16#usize) ×
    (Array (Array Std.U8 32#usize) 16#usize) × (Option Bool)))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepU32 iter
  match o with
  | none =>
    if n = 1#usize
    then
      let i ← multiproof.index_at idx 0#usize
      if i = 0#u32
      then
        let b ← multiproof.root_matches val root
        if b
        then let i1 := Slice.len nodes
             ok (done (idx, val, some (at1 = i1)))
        else ok (done (idx, val, some false))
      else ok (done (idx, val, some false))
    else ok (done (idx, val, some false))
  | some _ =>
    let (arity1, idx1, val1, n1, at2, pending_return1, i) ←
      ops.level
        arity idx val n nodes at1 0#usize 0#usize pending_return
    match i with
    | 1#uscalar =>
      ok (cont (iter1, arity1, idx1, val1, n1, at2, pending_return1))
    | _ =>
      match pending_return1 with
      | none => ok (done (idx1, val1, none))
      | some _ => ok (done (idx1, val1, pending_return1))

end AspisR1Stage2.R13SourceTerminal
