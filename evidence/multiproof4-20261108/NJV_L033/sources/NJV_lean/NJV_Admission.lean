import NJV_NativeEntry
import NJV_LevelDomains
import NJV_WordDomains

set_option autoImplicit false
noncomputable section
namespace NJV_Admission
open Aeneas Aeneas.Std Result NJP_DigestCarrier NJP_ScratchCarrier
open MultiproofConeRef

/-- Every native row cut in this invocation is admitted at its own prestate.
This relation is a CONCLUSION of all, not an extra root hypothesis. -/
inductive Admissible (H : NJP_RowModel.Request → NJP_RowModel.Digest)
    (root : RefDigest) (physical : Slice U8) (s : reference.Scratch) :
    List (NJP_RowModel.Request × NJP_RowModel.Digest) → (Bool × NJP_RowModel.Scratch) → Prop where
 | rejected (guard : ¬NJV_Entry.Guard physical s) : Admissible H root physical s [] (false,raw s)
 | returned (events : List (NJP_RowModel.Request × NJP_RowModel.Digest)) (out : NJP_LoopModel.Level)
     (guard : NJV_Entry.Guard physical s)
     (levels : NJV_LevelDomains.Admissible H (fun n => physical.val[n]!) physical.val.length
       18 {raw s with cursor:=0} events out) :
   Admissible H root physical s events (NJP_LoopModel.finish (decode root) physical.val.length out)

theorem all (H : NJP_RowModel.Request → NJP_RowModel.Digest) (root : RefDigest)
    (physical : Slice U8) (s : reference.Scratch) (bytes : physical.val.length≤9216)
    (events : List (NJP_RowModel.Request × NJP_RowModel.Digest)) (out : Bool × NJP_RowModel.Scratch)
    (native : NJV_NativeEntry.Invocation H root physical s events out) :
 Admissible H root physical s events out := by
 cases native with
 | rejected guard => exact .rejected guard
 | returned events out guard levels =>
   have d := NJV_Entry.guard_domain physical s guard
   have domain : NJP_LoopTotal.LevelDomain physical.val.length {raw s with cursor:=0} :=
     ⟨d.1,d.2,by simp,bytes⟩
   exact .returned events out guard (NJV_LevelDomains.all H _ _ _ _ _ _ levels domain)

#print all
#print axioms all
end NJV_Admission
end
