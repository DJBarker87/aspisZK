import RPz7_F3T_ProofCarriers
set_option autoImplicit false
namespace AspisR1.F3T_RootAgreement
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OraclePortCompactDraft

theorem from_bytes (p : Parsed) (root : State) (same : bytes root=root0 p) :
    root=fun j=>(root0 p)[j.val]?.getD 0 := by
  funext j
  rw [← same]
  simp only [bytes,List.getElem?_ofFn,dif_pos j.isLt,Option.getD_some]

#print axioms from_bytes
end AspisR1.F3T_RootAgreement
