import NJV_Pending

set_option autoImplicit false
noncomputable section
namespace NJV_PendingBind
open Aeneas Aeneas.Std Result NJP_RowModel NJP_LoopModel
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- Prefix stability under a returning-result continuation. The pending call
has no answer, so the continuation is not entered at this boundary. -/
theorem pending_bind {α β : Type} (H : Request → Digest) (p : Program Request Digest α)
    (f : α → Program Request Digest β) (n : Nat) (history : List (Request × Digest)) (q : Request)
    (pending : NJP_AbortPrefix.pending H n p=some (history,q)) :
 NJP_AbortPrefix.pending H n (bind p f)=some (history,q) := by
 induction n generalizing p history q with
 | zero =>
   cases p with
   | done a => simp only [NJP_AbortPrefix.pending] at pending;contradiction
   | ask r next =>
     simpa only [AspisV8R19.OracleProgramOps.bind,NJP_AbortPrefix.pending] using pending
 | succ n ih =>
   cases p with
   | done a => simp only [NJP_AbortPrefix.pending] at pending;contradiction
   | ask r next =>
     simp only [NJP_AbortPrefix.pending] at pending
     cases h : NJP_AbortPrefix.pending H n (next (H r)) with
     | none => simp only [h,Option.map_none] at pending;contradiction
     | some pair =>
       obtain ⟨events,last⟩ := pair
       have tail := ih (next (H r)) events last h
       simpa only [AspisV8R19.OracleProgramOps.bind,NJP_AbortPrefix.pending,tail,h] using pending

/-- A known returning prefix is concatenated before a later pending call.
No H(q) is consumed for that last unanswered request. -/
theorem after_return {α β : Type} (H : Request → Digest) (p : Program Request Digest α)
    (f : α → Program Request Digest β) (first rest : List (Request × Digest)) (a : α)
    (n : Nat) (q : Request) (returned : eval H p=(first,a))
    (pending : NJP_AbortPrefix.pending H n (f a)=some (rest,q)) :
 NJP_AbortPrefix.pending H (first.length+n) (bind p f)=some (first++rest,q) := by
 induction p generalizing first with
 | done a' =>
   simp only [eval] at returned
   have eqs := Prod.mk.inj returned
   obtain ⟨rfl,rfl⟩ := eqs
   simpa only [AspisV8R19.OracleProgramOps.bind,List.length_nil,Nat.zero_add,List.nil_append] using pending
 | ask r next ih =>
   simp only [eval] at returned
   have firstEq := congrArg Prod.fst returned
   have valueEq := congrArg Prod.snd returned
   dsimp only at firstEq valueEq
   have tailReturned : eval H (next (H r))=((eval H (next (H r))).1,a) := Prod.ext rfl valueEq
   have tail := ih (H r) (eval H (next (H r))).1 tailReturned
   rw [←firstEq]
   simp only [List.length_cons]
   rw [Nat.add_right_comm _ 1 n]
   simp only [AspisV8R19.OracleProgramOps.bind,NJP_AbortPrefix.pending,tail,Option.map_some,List.cons_append]

#print pending_bind
#print axioms pending_bind
#print after_return
#print axioms after_return
end NJV_PendingBind
end
