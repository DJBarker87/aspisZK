import NLH_SemanticChild0
import NLH_SemanticChild1
import NLH_SemanticChild2
import NLH_SemanticChild3
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLH_SemanticPrefix
open Aeneas Aeneas.Std Result FIq_Native NLH_SemanticState
open NKI_InitialPrefix (Public Openings Selectors)
def stage {pub o s} (p : NKR_TermSemanticSource.Packet pub o s) (base : State) (n : Nat) : State :=
 {base with packed := match n with
  | 0 => NKR_TermSemanticSource.zero
  | 1 => p.schedule
  | 2 => p.path
  | 3 => p.value
  | _ => p.occupancy}
/-- One native parent carrier crosses the four source-ordered mutable-array
children, and each child's returned array becomes the next child's input. -/
theorem cuts (pub : Public) (o : Openings) (s : Selectors)
 (p : NKR_TermSemanticSource.Packet pub o s) (base : State) :
 NLH_FoldCore.Cuts (step pub o s) ((List.finRange 4).map Event.child)
  (stage p base 0) (ok (stage p base 4)) ((List.finRange 4).map Event.child) := by
 change NLH_FoldCore.Cuts _ [Event.child 0,Event.child 1,Event.child 2,Event.child 3] _ _ _
 exact .next (NLH_SemanticChild0.step pub o s p (stage p base 0) rfl)
  (.next (NLH_SemanticChild1.step pub o s p (stage p base 1) rfl)
   (.next (NLH_SemanticChild2.step pub o s p (stage p base 2) rfl)
    (.next (NLH_SemanticChild3.step pub o s p (stage p base 3) rfl) (.nil (stage p base 4)))))
#print axioms cuts
end AspisR1.NLH_SemanticPrefix
end
