import NIT_GuardResult
import NIT_SharedChain
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIT_GuardComposition
open Aeneas Aeneas.Std Result NIT_Cuts NIT_PairControl
open NIT_GuardResult (from_cut)
open NIT_ErrorTransport (unitReply)

def dispatch (guard : RU) (tail : Result NR) : Result NR :=
 match guard with | .Err e=>ok (.Err e) | .Ok _=>tail

/-- Native error-prefix composition is determined by the cut, including the
full error identity, rather than a premise about the final pair result. -/
theorem rejected (b : Bool) (l : SameGuard) (e : FIo_Native.verifier.Error)
 (p h out : RU) (tail : Result NR)
 (r : l.regular=unitReply (.Err e)) (hp : l.«partial»=unitReply p)
 (hh : l.high=unitReply h) (cut : cutSameGuard b l (unitReply out)) :
 dispatch out tail=ok (.Err e) := by
 rw [from_cut b l (.Err e) p h out r hp hh cut]
 rfl

theorem unshared (l : SameGuard) (p h out : RU) (tail : Result NR)
 (r : l.regular=unitReply (.Ok ())) (hp : l.«partial»=unitReply p)
 (hh : l.high=unitReply h) (cut : cutSameGuard false l (unitReply out)) :
 dispatch out tail=tail := by
 rw [from_cut false l (.Ok ()) p h out r hp hh cut]
 rfl

theorem partial_rejected (l : SameGuard) (e : FIo_Native.verifier.Error)
 (h out : RU) (tail : Result NR)
 (r : l.regular=unitReply (.Ok ())) (hp : l.«partial»=unitReply (.Err e))
 (hh : l.high=unitReply h) (cut : cutSameGuard true l (unitReply out)) :
 dispatch out tail=ok (.Err e) := by
 rw [from_cut true l (.Ok ()) (.Err e) h out r hp hh cut]
 rfl

theorem high (l : SameGuard) (h out : RU) (tail : Result NR)
 (r : l.regular=unitReply (.Ok ())) (hp : l.«partial»=unitReply (.Ok ()))
 (hh : l.high=unitReply h) (cut : cutSameGuard true l (unitReply out)) :
 dispatch out tail=dispatch h tail := by
 rw [from_cut true l (.Ok ()) (.Ok ()) h out r hp hh cut]
 cases h <;> rfl

#print axioms rejected
#print axioms unshared
#print axioms partial_rejected
#print axioms high
end AspisR1.NIT_GuardComposition
