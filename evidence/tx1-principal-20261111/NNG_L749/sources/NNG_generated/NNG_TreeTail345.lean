import NNG_TreeBase345
import NMT_345BoundsFold
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_TreeTail345
open Aeneas Aeneas.Std Result NMT_345 NMT_CallTree NNG_TreeBase345
abbrev ChildArgs := Public × Slice U8 × Slice U8 × Usize

def tryChild (args : ChildArgs) (r : Result Ret) (next : alloc.vec.Vec U8 → Code Ret) : Code Ret := do
 let value ← invoke "TX1:328/first_decoded" args r
 match value with | .Ok a=>next a | .Err e=>pure (.Err e)

theorem erase_child (args : ChildArgs) (r : Result Ret) (next : alloc.vec.Vec U8 → Code Ret) :
 erase (tryChild args r next)=tryStep r (fun a=>erase (next a)) := by
 unfold tryChild tryStep
 simp only [Bind.bind]
 rw [erase_bind,erase_invoke]
 apply result_congr
 intro reply
 cases reply <;> rfl
#print axioms erase_child

def tail {W : Type} (c : Calls) (s : Bounds W) : Code Ret := do
 if Slice.len s.proofData != s.proofEnd then pure (.Err .InvalidAccountData) else do
  let proofPrefix ← (liftM (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
    s.proofData {«end»:=s.proofStart}) : Code _)
  let mismatch ← (liftM (c.c0 core.cmp.PartialEqU8 proofPrefix s.candidate) : Code _)
  if mismatch then pure (.Err .InvalidAccountData) else do
   let offset ← (liftM (Usize.wrapping_add s.proofStart 8#usize) : Code _)
   let tag ← (liftM (Slice.index_usize s.proofData offset) : Code _)
   let expected ← (liftM (c.c3 NMT_stage1_owned.aspis_r1_cost_probe.transport.Variant.S2) : Code _)
   if tag != expected then pure (.Err .InvalidAccountData) else do
    let pub ← (liftM (c.c5 s.statement) : Code _)
    let proof ← (liftM (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      s.proofData {start:=s.proofStart,«end»:=s.proofEnd}) : Code _)
    let kbyte ← (liftM (Slice.index_usize s.data 1#usize) : Code _)
    let k := UScalar.cast .Usize kbyte
    tryChild (pub,s.publicData,proof,k) (c.c11 pub s.publicData proof k) fun checkpoint=>
     if alloc.vec.Vec.len checkpoint != Slice.len s.checkpointData
     then pure (.Err .InvalidAccountData) else pure (.Ok checkpoint)

theorem erase_tail {W : Type} (c : Calls) (s : Bounds W) : erase (tail c s)=tailFold c s := by
 unfold tail tailFold
 simp only [Bind.bind,erase_bind,erase_lift,erase_pure,erase_child]
 repeat' first | rfl | (split <;> simp only [erase_bind,erase_lift,erase_pure,erase_child])
#print axioms erase_tail

def bounds {W : Type} (c : Calls) (s : ProofData W) : Code Ret := do
 let length ← (liftM c.c4 : Code Usize)
 let start ← (liftM c.c8 : Code Usize)
 let sum := Usize.checked_add start length
 tryCode (NMT_stage1_owned.core.option.Option.ok_or sum NMT_stage1_owned.solana_program_error.ProgramError.InvalidAccountData)
  (fun end_=>tail c ⟨s,start,end_⟩)

theorem erase_bounds {W : Type} (c : Calls) (s : ProofData W) : erase (bounds c s)=boundsFold c s := by
 unfold bounds boundsFold
 simp only [Bind.bind,erase_bind,erase_lift,erase_try,erase_tail]
#print axioms erase_bounds
end AspisR1.NNG_TreeTail345
