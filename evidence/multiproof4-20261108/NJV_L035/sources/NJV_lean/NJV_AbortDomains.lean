import NJV_AbortEntry
import NJV_LevelDomains

set_option autoImplicit false
noncomputable section
namespace NJV_AbortDomains
open Aeneas Aeneas.Std Result NJP_RowModel NJP_LoopModel NJP_LoopTotal
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

def LastDomain (nodes : Nat → U8) (length : Nat) (q : Request) (pending : Scratch) : Prop :=
 ∃ (before : Scratch) (i w : Nat), Domain length before i w ∧ NJV_Pending.Cut before i length nodes pending q

theorem rows (H : Request → Digest) (nodes : Nat → U8) (length fuel : Nat)
    (s : Scratch) (i w : Nat) (events : List (Request × Digest)) (q : Request) (pending : Scratch)
    (native : NJV_AbortRows.Invocation H nodes length fuel s i w events q pending)
    (domain : Domain length s i w) : LastDomain nodes length q pending := by
 induction native with
 | here fuel s pending i w q cut => exact ⟨s,i,w,domain,cut⟩
 | next fuel s after i w ni nw log events q pending active cut tail ih =>
   have nextDomain := NJV_RowDomains.next_domain H nodes length s after i w ni nw log domain active cut
   exact ih nextDomain.2.1

theorem levels (H : Request → Digest) (nodes : Nat → U8) (length height : Nat)
    (s : Scratch) (events : List (Request × Digest)) (q : Request) (pending : Scratch)
    (native : NJV_AbortLevels.Invocation H nodes length height s events q pending)
    (domain : LevelDomain length s) : LastDomain nodes length q pending := by
 induction native with
 | here height s pending events q row =>
   exact rows H nodes length s.n s 0 0 events q pending row
     ⟨domain.1,domain.2.1,by omega,by omega,domain.2.2.1,domain.2.2.2⟩
 | next height s after pending first rest q row tail ih =>
   have progress := NJV_LevelDomains.progress H nodes length s first (.done after) row domain
   exact ih progress.1

theorem entry (H : NJP_RequestTransport.Address → NJP_DigestCarrier.RefDigest)
    (root : NJP_DigestCarrier.RefDigest) (physical : Slice U8) (s : MultiproofConeRef.reference.Scratch)
    (bytes : physical.val.length≤9216) (events : List (Request × Digest)) (q : Request) (pending : Scratch)
    (native : NJV_AbortEntry.Invocation (NJP_RequestTransport.hash H) root physical s events q pending) :
 LastDomain (fun n => physical.val[n]!) physical.val.length q pending := by
 have d := NJV_Entry.guard_domain physical s native.guard
 exact levels (NJP_RequestTransport.hash H) _ _ _ _ _ _ _ native.levels
   ⟨d.1,d.2,by simp,bytes⟩

#print rows
#print axioms rows
#print levels
#print axioms levels
#print entry
#print axioms entry
end NJV_AbortDomains
end
