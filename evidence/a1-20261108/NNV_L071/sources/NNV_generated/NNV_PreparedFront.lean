import NNV_PrepareFrontCut
import NNV_PreparedNative
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_PreparedFront
open RSL NNH_Libraries
/-- Successful canonical prepare determines the SAME semantic, View and scratch.
No native result or representation assumption enters. -/
theorem returned (a : TX1_087.Args VL) (env : Env) (p : VL.Prepared) (g : VL.E29)
 (called : NNH_Tx1Returns.preparedValue a env = .ok (p,g)) :
 ∃ sem v, Nonempty (NNV_PrepareFrontCut.Packet a env sem v) ∧
 LIB_Prepared.value (sem,v,a.g) env = (.ok p,g) := by
 unfold NNH_Tx1Returns.preparedValue NNH_PrepareReturns.value at called
 cases front : NNH_PrepareReturns.frontValue a env with
 | error e => rw [front] at called; cases called
 | ok pair =>
  rw [front] at called
  cases prep : LIB_Prepared.value (pair.1,pair.2,a.g) env with
  | mk reply scratch =>
   rw [prep] at called
   cases reply with
   | error e => cases called
   | ok out =>
    have same : (out,scratch)=(p,g) := Except.ok.inj called
    cases same
    exact ⟨pair.1,pair.2,NNV_PrepareFrontCut.returned a env pair.1 pair.2 front,prep⟩
#print axioms returned
end AspisR1.NNV_PreparedFront
end
