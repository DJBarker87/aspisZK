import NJV_Entry
import NJV_NativeLevels

set_option autoImplicit false
noncomputable section
namespace NJV_NativeEntry
open Aeneas Aeneas.Std Result NJP_DigestCarrier NJP_ScratchCarrier NJP_CohortWrite
open MultiproofConeRef
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- Complete binary native entry, after CLOSED well_formed/parent/root replies
are installed at SAME arguments. Constructors transcribe the early entry and
terminal cuts plus the nested native cut chain, never a whole endpoint law.
The Kani-to-constructor association is P6/D188 option-A transport. -/
inductive Invocation (H : NJP_RowModel.Request → NJP_RowModel.Digest)
    (root : RefDigest) (physical : Slice U8) (s : reference.Scratch) :
    List (NJP_RowModel.Request × NJP_RowModel.Digest) → (Bool × NJP_RowModel.Scratch) → Prop where
 | rejected (guard : ¬NJV_Entry.Guard physical s) :
   Invocation H root physical s [] (false,raw s)
 | returned (history : List (NJP_RowModel.Request × NJP_RowModel.Digest)) (out : NJP_LoopModel.Level)
     (guard : NJV_Entry.Guard physical s)
     (levels : NJV_NativeLevels.Invocation H (fun n => physical.val[n]!) physical.val.length
       18 {raw s with cursor:=0} history out) :
   Invocation H root physical s history (NJP_LoopModel.finish (decode root) physical.val.length out)

theorem raw_observation (H : NJP_RowModel.Request → NJP_RowModel.Digest)
    (root : RefDigest) (physical : Slice U8) (s : reference.Scratch)
    (history : List (NJP_RowModel.Request × NJP_RowModel.Digest)) (out : Bool × NJP_RowModel.Scratch)
    (native : Invocation H root physical s history out) :
 eval H (NJV_Entry.rawProgram root physical s)=(history,ok out) := by
 cases native with
 | rejected guard => simp only [NJV_Entry.rawProgram,if_neg guard,eval]
 | returned history out guard levels =>
   simp only [NJV_Entry.rawProgram,if_pos guard]
   exact NJV_NativeLevels.returning H _ _ _ _ _ _ levels

/-- Full typed observation equals this exact native invocation; the raw carrier
is faithful to all sixteen indices and all 512 digest bytes, not live cells only. -/
theorem observation (H : Slice (Slice U8) → RefDigest) (root : RefDigest)
    (physical : Slice U8) (s : reference.Scratch)
    (history : List (NJP_RowModel.Request × NJP_RowModel.Digest)) (out : Bool × NJP_RowModel.Scratch)
    (native : Invocation (NJP_RequestTransport.hash H) root physical s history out) :
 let typed := eval H (NJV_Entry.program root physical s)
 (typed.1,mapResult NJP_CohortReturning.answer typed.2)=
 (history.map (fun e => (NJP_RequestTransport.address e.1,encode e.2)),ok out) := by
 dsimp only
 rw [NJV_Entry.observation,NJP_RequestTransport.observation,
   raw_observation _ _ _ _ _ _ native]

#print raw_observation
#print axioms raw_observation
#print observation
#print axioms observation
end NJV_NativeEntry
end
