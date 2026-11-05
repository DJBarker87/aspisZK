import NIT_PairDomain
import NGM_GuardRawModel
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIT_ControlCuts
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts

/-- The CLOSED raw guard packet is installed on the SAME owner and folds2. -/
theorem guard (w : W) :
 FIo_Native.weights.shared_two_point_guard w 2#usize=ok (NGM_GuardExact.guard w 2#usize) ∧
 NGM_GuardRef.guard_raw_ref (NGM_GuardRawModel.variant w.variant) 2#usize
  (NGM_GuardRawModel.rowArray (NGM_GuardExact.row w 0 2))
  (NGM_GuardRawModel.rowArray (NGM_GuardExact.row w 2 2))
  (NGM_GuardRawModel.rowArray (NGM_GuardExact.row w 0 3))
  (NGM_GuardRawModel.rowArray (NGM_GuardExact.row w 2 3))=
  ok (NGM_GuardExact.guard w 2#usize) := by
 have source := NGM_GuardExact.source w 2#usize
 exact ⟨source,(NGM_GuardRawModel.cohort w 2#usize).trans source⟩

/-- A cut-local log for every Bool and all error arms; unused replies remain
arbitrary parameters, not silently successful children. -/
theorem same_guard (shared : Bool) (regular partialReply high : Reply Unit) :
 ∃ l : SameGuard,l.regular=regular ∧ l.«partial»=partialReply ∧ l.high=high ∧
 cutSameGuard shared l (sameExpected shared l).1 := by
 cases regular with
 | Err e =>
  let l : SameGuard := ⟨shared,.Err e,partialReply,high,(fun i=>[0][i]?.getD 99),1⟩
  exact ⟨l,rfl,rfl,rfl,by simp [cutSameGuard,sameExpected,l]⟩
 | Ok u =>
  cases u
  cases shared with
  | false =>
   let l : SameGuard := ⟨false,.Ok (),partialReply,high,(fun i=>[0,4][i]?.getD 99),2⟩
   exact ⟨l,rfl,rfl,rfl,by simp [cutSameGuard,sameExpected,l]⟩
  | true =>
   cases partialReply with
   | Err e =>
    let l : SameGuard := ⟨true,.Ok (),.Err e,high,(fun i=>[0,1,2][i]?.getD 99),3⟩
    exact ⟨l,rfl,rfl,rfl,by simp [cutSameGuard,sameExpected,l]⟩
   | Ok u =>
    cases u
    cases high with
    | Err e =>
     let l : SameGuard := ⟨true,.Ok (),.Ok (),.Err e,(fun i=>[0,1,2,3][i]?.getD 99),4⟩
     exact ⟨l,rfl,rfl,rfl,by simp [cutSameGuard,sameExpected,l]⟩
    | Ok u =>
     cases u
     let l : SameGuard := ⟨true,.Ok (),.Ok (),.Ok (),(fun i=>[0,1,2,3,4][i]?.getD 99),5⟩
     exact ⟨l,rfl,rfl,rfl,by simp [cutSameGuard,sameExpected,l]⟩

/-- Construct the pinned selected-argument observation on the exact arrays and
post-payloads. A whole-body execution join is not assumed. -/
theorem edges (w : Ref W) (alpha : Ref (Array E 2#usize)) (f : Ref (Slice U8))
 (scratch : Ref (Array K 64#usize)) (parts : Ref Parts) (ap0 ap1 : Powers)
 (common : Ref CommonCells) (shared : Bool) (power i : Nat)
 (post : Parts) (partials : Powers)
 (s2 : w.value.variant=FIo_Native.transport.Variant.S2) (size : f.value.val.length=2048)
 (ca : canonical alpha.value) (c0 : canonical ap0) (c1 : canonical ap1)
 (cp : canonical parts.value) (cr : canonical post) (cc : canonical partials)
 (hp : power<4) (hi : i<16) :
 ∃ l : PairEdges,cutPairEdges w alpha f scratch parts ap0 ap1 common shared power i l ∧
 l.regular_post=post ∧ l.partial_reply=partials := by
 let l : PairEdges := ⟨w.address,alpha.address,f.address,scratch.address,parts.address,
  common.address,f.address,w.address,parts.address,shared,2,64,2,2048,64,2048,
  epick ap0 power,epick ap1 power,epick partials power,epick ap0 power,epick ap1 power,
  kpick common.value i,post,partials⟩
 refine ⟨l,?_,rfl,rfl⟩
 exact ⟨s2,hp,hi,ca,c0,c1,cp,cr,cc,size,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,
  fun _=>⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩⟩

#print axioms guard
#print axioms same_guard
#print axioms edges
end AspisR1.NIT_ControlCuts
