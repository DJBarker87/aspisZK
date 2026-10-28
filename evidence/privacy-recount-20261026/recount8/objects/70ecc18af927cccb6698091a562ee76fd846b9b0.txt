import R1Z.PV_RDEAC_PartialHeaders
open Aeneas Aeneas.Std
namespace R1Z.PV_RDEAC_FreeWord
open PV_RDB1_V183_ReserveWorld

/-- Auxiliary size word only; the full world, free addresses and private
allocator state remain in finalWorld and its explicitly applied primitive. -/
def releaseWord (cap : Nat) : List Nat := if cap=0 then [] else [cap]

def word {S F : Type} (owned : Buffer U8) (e : Execution U8 S F) : List Nat :=
  match e.returned with
  | .error (.allocError _) => []
  | .error .capacityOverflow => releaseWord e.buffer.capacity++releaseWord owned.capacity
  | .ok () => releaseWord owned.capacity

theorem release_count {S F : Type} (free : Nat → Nat → Nat → S → S)
    (owned : Buffer U8) (w : World S F) :
    (PV_RDEAC_OwnedCleanup.release free owned w).deallocCalls=w.deallocCalls+(releaseWord owned.capacity).length := by
  unfold PV_RDEAC_OwnedCleanup.release releaseWord
  split <;> simp only [List.length_nil,List.length_cons,Nat.add_zero]

theorem final_count {S F : Type} (free : Nat → Nat → Nat → S → S)
    (owned : Buffer U8) (e : Execution U8 S F) :
    (PV_RDEAC_JoinHandlers.finalWorld free owned e).deallocCalls=e.world.deallocCalls+(word owned e).length := by
  cases e with
  | mk returned b w =>
    cases returned with
    | error err =>
      cases err <;> simp only [PV_RDEAC_JoinHandlers.finalWorld,word,release_count,
        List.length_nil,List.length_append,Nat.add_zero,Nat.add_assoc]
    | ok unit => exact release_count free owned w

theorem owned_word (cap : Nat) (h : cap=69) : releaseWord cap=[69] := by
  subst cap
  rfl

/-- Every possible partialCap-buffer cleanup header is determined by the public
base length and the source's separator-growth formula. Abort and success arms
are explicit; the failure-selected prefix belongs to primitive adequacy. -/
theorem source_headers {S F : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (address : Nat) (needSep : Bool) (base path : List U8)
    (w : World S F) (owned : Buffer U8) (cap : owned.capacity=69) :
    let e := PV_RDEAC_FullJoin.join step shape address false needSep base path w
    word owned e=[] ∨ word owned e=[69] ∨
      ∃ partialCap, (partialCap=0 ∨ partialCap=base.length ∨ partialCap=PV_RDEA_AppendRequests.nextCapacity base.length base.length 1) ∧
        word owned e=releaseWord partialCap++[69] := by
  dsimp only
  let e := PV_RDEAC_FullJoin.join step shape address false needSep base path w
  change word owned e=[] ∨ word owned e=[69] ∨ _
  cases h : e.returned with
  | error err =>
    cases err with
    | allocError layout => exact Or.inl (by simp only [word,h])
    | capacityOverflow =>
      have headers := PV_RDEAC_PartialHeaders.join_error step shape address needSep base path w .capacityOverflow h
      have hw : word owned e=releaseWord e.buffer.capacity++[69] := by simp only [word,h,owned_word _ cap]
      exact Or.inr (Or.inr ⟨e.buffer.capacity,headers,hw⟩)
  | ok unit => exact Or.inr (Or.inl (by simp only [word,h,owned_word _ cap]))

#print axioms release_count
#print axioms final_count
#print axioms owned_word
#print axioms source_headers
end R1Z.PV_RDEAC_FreeWord
