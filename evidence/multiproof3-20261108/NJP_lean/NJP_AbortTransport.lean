import NJP_AbortPrefix
import NJP_RequestTransport

set_option autoImplicit false
noncomputable section
namespace NJP_AbortTransport
open Aeneas Aeneas.Std NJP_RowModel NJP_DigestCarrier
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

def physicalPending {α : Type} (H : NJP_RequestTransport.Address → RefDigest) :
 Nat → Program NJP_RequestTransport.Address RefDigest α →
 Option (List (NJP_RequestTransport.Address × RefDigest) × NJP_RequestTransport.Address)
 | 0,.done _ => none
 | 0,.ask q _ => some ([],q)
 | n+1,.done _ => none
 | n+1,.ask q next => (physicalPending H n (next (H q))).map
     fun (history,last) => ((q,H q)::history,last)

def history (events : List (Request × Digest)) :=
 events.map (fun event => (NJP_RequestTransport.address event.1,encode event.2))

theorem same {α : Type} (H : NJP_RequestTransport.Address → RefDigest) (n : Nat)
    (p : Program Request Digest α) :
 physicalPending H n (NJP_RequestTransport.transport p)=
 (NJP_AbortPrefix.pending (NJP_RequestTransport.hash H) n p).map
   (fun (events,last) => (history events,NJP_RequestTransport.address last)) := by
 induction n generalizing p with
 | zero => cases p <;> rfl
 | succ n ih =>
   cases p with
   | done x => rfl
   | ask q next =>
     simp only [physicalPending,NJP_RequestTransport.transport,NJP_AbortPrefix.pending,
       NJP_RequestTransport.hash,ih,Option.map_map]
     congr 1
     funext pair
     rcases pair with ⟨events,last⟩
     simp only [Function.comp_apply,history,List.map_cons,encode_decode,NJP_RequestTransport.hash]

/-- Aborting query has no answer, and only the prior exact replies are mapped. -/
theorem abort_prefix {α : Type} (H : NJP_RequestTransport.Address → RefDigest) (n : Nat)
    (p : Program Request Digest α) (events : List (Request × Digest)) (last : Request)
    (aborted : NJP_AbortPrefix.pending (NJP_RequestTransport.hash H) n p=some (events,last)) :
 physicalPending H n (NJP_RequestTransport.transport p)=
 some (history events,NJP_RequestTransport.address last) ∧
 history events=(eval H (NJP_RequestTransport.transport p)).1.take n ∧ events.length=n := by
 constructor
 · rw [same,aborted];rfl
 · obtain ⟨sameEvents,length,_⟩ := NJP_AbortPrefix.exact_prefix _ n p events last aborted
   rw [NJP_RequestTransport.observation]
   dsimp only
   constructor
   · rw [history,sameEvents,List.map_take]
   · exact length

#print same
#print axioms same
#print abort_prefix
#print axioms abort_prefix
end NJP_AbortTransport
end
