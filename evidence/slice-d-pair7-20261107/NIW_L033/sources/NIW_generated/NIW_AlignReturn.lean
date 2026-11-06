import NIW_AlignFinal
import NIT_PortInstantiation
import NIT_GuardFrontJoin
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignReturn
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_PairControl

def FinalCuts (parts powers : Parts) (sums : Nat → E) (logs : Nat → Final) : Prop :=
 ∀ j,j<7 → cutFinal parts powers j (sums j) (logs j) (sums (j+1))

/-- Canonicality of the actual last native sum follows from its observed last
cut, without choosing a successful model packet result. -/
theorem final_canonical (parts powers : Parts) (sums : Nat → E) (logs : Nat → Final)
 (native : FinalCuts parts powers sums logs) : canonE (sums 7) := by
 have cut := native 6 (by decide)
 rcases cut with ⟨_,_,_,_,_,canonical,_,_,_,_,_,_,after⟩
 rw [after]
 exact canonical

theorem return_cut (parts powers : Parts) (sums : Nat → E) (logs : Nat → Final)
 (native : FinalCuts parts powers sums logs) : NIT_TailCuts.returnCut (sums 7) (.Ok (sums 7)) :=
 ⟨final_canonical parts powers sums logs native,rfl⟩

/-- Only an entered final fold needs logs. Rejected guard prefixes require no
facts at all about the unentered final sum, powers, parts or replies. -/
theorem guarded_canonical (guard : RU) (parts powers : Parts) (sums : Nat → E) (logs : Nat → Final)
 (entered : guard=.Ok () → FinalCuts parts powers sums logs) :
 NIT_ResultCanonical.Canonical (NIT_GuardComposition.dispatch guard (ok (.Ok (sums 7)))) := by
 cases guard with
 | Err e=>trivial
 | Ok u=>cases u;exact final_canonical parts powers sums logs (entered rfl)

def portReply (guard : RU) (sum : E) : Reply FE :=
 match guard with | .Err e=>.Err (FIo_Install.error e) | .Ok _=>.Ok (FIo_Install.fromE sum)

/-- PairPort's returning canonicality can be discharged from actual native
sum cuts and guard replies. The complete native pair Result association is
still required before this expression may be identified with PairPort.reply. -/
theorem port_canonical (guard : RU) (parts powers : Parts) (sums : Nat → E) (logs : Nat → Final)
 (entered : guard=.Ok () → FinalCuts parts powers sums logs) :
 replyCanonical (portReply guard (sums 7)) := by
 cases guard with
 | Err e=>trivial
 | Ok u=>
  cases u
  exact NIT_PortInstantiation.canonical_reply (.Ok (sums 7))
   (final_canonical parts powers sums logs (entered rfl))

#print axioms final_canonical
#print axioms return_cut
#print axioms guarded_canonical
#print axioms port_canonical
end AspisR1.NIW_AlignReturn
