import NLH_ScalarStep00
import NLH_ScalarStep01
import NLH_ScalarStep02
import NLH_ScalarStep03
import NLH_ScalarStep04
import NLH_ScalarStep05
import NLH_ScalarStep06
import NLH_ScalarStep07
import NLH_ScalarStep08
import NLH_ScalarStep09
import NLH_ScalarStep10
import NLH_ScalarStep11
import NLH_ScalarFrame
import NLH_SemanticState
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLH_ScalarChain
open Aeneas Aeneas.Std Result FIq_Native
open NKR_TermScalarInvocation (Packet)
open NLH_ScalarDefs
/-- Intermediate induction lemma; its Packet is constructed internally by a
future row root. It is not a row root and earns no standalone native credit. -/
theorem call_ready {pub o s before} (p : Packet pub o s before) (st : State)
 (i : Fin 12) (ready : Ready p st i) : call pub o s st i=ok (values p i) := by
 fin_cases i
 · exact NLH_ScalarStep00.call_ready p st ready
 · exact NLH_ScalarStep01.call_ready p st ready
 · exact NLH_ScalarStep02.call_ready p st ready
 · exact NLH_ScalarStep03.call_ready p st ready
 · exact NLH_ScalarStep04.call_ready p st ready
 · exact NLH_ScalarStep05.call_ready p st ready
 · exact NLH_ScalarStep06.call_ready p st ready
 · exact NLH_ScalarStep07.call_ready p st ready
 · exact NLH_ScalarStep08.call_ready p st ready
 · exact NLH_ScalarStep09.call_ready p st ready
 · exact NLH_ScalarStep10.call_ready p st ready
 · exact NLH_ScalarStep11.call_ready p st ready
def stage {pub o s before} (p : Packet pub o s before) (base : NLH_SemanticState.State) (n : Nat) : NLH_SemanticState.State :=
 {base with locals := snapshot p n}
theorem step {pub o s before} (p : Packet pub o s before) (base : NLH_SemanticState.State) (i : Fin 12) :
 NLH_SemanticState.step pub o s (.field i) (stage p base i.val)=ok (stage p base (i.val+1)) := by
 have ready : Ready p (snapshot p i.val) i := by intro j h;exact if_pos h
 have h := call_ready p (snapshot p i.val) i ready
 change (do let reply ← call pub o s (snapshot p i.val) i
            ok {base with locals := fun j => if j=i then reply else snapshot p i.val j})=_
 rw [h,bind_tc_ok,NLH_ScalarFrame.update]
 rfl
/-- One state is carried through all twelve native one-statement windows.
Every earlier operand and every future-local frame comes from that state. -/
theorem fields {pub o s before} (p : Packet pub o s before) (base : NLH_SemanticState.State) :
 NLH_FoldCore.Cuts (NLH_SemanticState.step pub o s)
  ((List.finRange 12).map NLH_SemanticState.Event.field) (stage p base 0) (ok (stage p base 12))
  ((List.finRange 12).map NLH_SemanticState.Event.field) := by
 change NLH_FoldCore.Cuts _ [NLH_SemanticState.Event.field 0,NLH_SemanticState.Event.field 1,NLH_SemanticState.Event.field 2,NLH_SemanticState.Event.field 3,NLH_SemanticState.Event.field 4,NLH_SemanticState.Event.field 5,NLH_SemanticState.Event.field 6,NLH_SemanticState.Event.field 7,NLH_SemanticState.Event.field 8,NLH_SemanticState.Event.field 9,NLH_SemanticState.Event.field 10,NLH_SemanticState.Event.field 11] _ _ _
 exact (.next (step p base 0) (.next (step p base 1) (.next (step p base 2) (.next (step p base 3) (.next (step p base 4) (.next (step p base 5) (.next (step p base 6) (.next (step p base 7) (.next (step p base 8) (.next (step p base 9) (.next (step p base 10) (.next (step p base 11) (.nil (stage p base 12))))))))))))))
theorem complete_locals {pub o s before} (p : Packet pub o s before) (base : NLH_SemanticState.State) :
 (stage p base 12).locals=values p := by
 funext j
 exact if_pos j.isLt
#print axioms call_ready
#print axioms step
#print axioms fields
#print axioms complete_locals
end AspisR1.NLH_ScalarChain
end
