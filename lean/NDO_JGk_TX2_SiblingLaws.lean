import NDO_JGk_TX2_Lookup00
import NDO_JGk_TX2_Lookup01
import NDO_JGk_TX2_Lookup02
import NDO_JGk_TX2_Lookup03
import NDO_JGk_TX2_Lookup04
import NDO_JGk_TX2_Lookup05
import NDO_JGk_TX2_Lookup06
import NDO_JGk_TX2_Lookup07
import NDO_JGk_TX2_Lookup08
import NDO_JGk_TX2_Lookup09
import NDO_JGk_TX2_Lookup10
import NDO_JGk_TX2_Lookup11
import NDO_JGk_TX2_Lookup12
import NDO_JGk_TX2_Lookup13
import NDO_JGk_TX2_Lookup14
import NDO_JGk_TX2_Lookup15
import NDO_JGk_TX2_Lookup16
import NDO_JGk_TX2_Lookup17
set_option autoImplicit false
namespace AspisR1.JGk_TX2_SiblingLaws
theorem source0 : JGf_TX2_M0Roots.SiblingLaw JGk_TX2_SiblingBase.native0 := by
  intro h hh b hb
  interval_cases h
  · exact JGk_TX2_Lookup00.source0 b hb
  · exact JGk_TX2_Lookup01.source0 b hb
  · exact JGk_TX2_Lookup02.source0 b hb
  · exact JGk_TX2_Lookup03.source0 b hb
  · exact JGk_TX2_Lookup04.source0 b hb
  · exact JGk_TX2_Lookup05.source0 b hb
  · exact JGk_TX2_Lookup06.source0 b hb
  · exact JGk_TX2_Lookup07.source0 b hb
  · exact JGk_TX2_Lookup08.source0 b hb
  · exact JGk_TX2_Lookup09.source0 b hb
  · exact JGk_TX2_Lookup10.source0 b hb
  · exact JGk_TX2_Lookup11.source0 b hb
  · exact JGk_TX2_Lookup12.source0 b hb
  · exact JGk_TX2_Lookup13.source0 b hb
  · exact JGk_TX2_Lookup14.source0 b hb
  · exact JGk_TX2_Lookup15.source0 b hb
  · exact JGk_TX2_Lookup16.source0 b hb
  · exact JGk_TX2_Lookup17.source0 b hb
#print axioms source0
theorem source1 : JGh_TX2_M1Roots.SiblingLaw JGk_TX2_SiblingBase.native1 := by
  intro h hh b hb
  interval_cases h
  · exact JGk_TX2_Lookup00.source1 b hb
  · exact JGk_TX2_Lookup01.source1 b hb
  · exact JGk_TX2_Lookup02.source1 b hb
  · exact JGk_TX2_Lookup03.source1 b hb
  · exact JGk_TX2_Lookup04.source1 b hb
  · exact JGk_TX2_Lookup05.source1 b hb
  · exact JGk_TX2_Lookup06.source1 b hb
  · exact JGk_TX2_Lookup07.source1 b hb
  · exact JGk_TX2_Lookup08.source1 b hb
  · exact JGk_TX2_Lookup09.source1 b hb
  · exact JGk_TX2_Lookup10.source1 b hb
  · exact JGk_TX2_Lookup11.source1 b hb
  · exact JGk_TX2_Lookup12.source1 b hb
  · exact JGk_TX2_Lookup13.source1 b hb
  · exact JGk_TX2_Lookup14.source1 b hb
  · exact JGk_TX2_Lookup15.source1 b hb
  · exact JGk_TX2_Lookup16.source1 b hb
  · exact JGk_TX2_Lookup17.source1 b hb
#print axioms source1
theorem source2 : JGc_TX2_M2Roots.SiblingLaw JGk_TX2_SiblingBase.native2 := by
  intro h hh b hb
  interval_cases h
  · exact JGk_TX2_Lookup00.source2 b hb
  · exact JGk_TX2_Lookup01.source2 b hb
  · exact JGk_TX2_Lookup02.source2 b hb
  · exact JGk_TX2_Lookup03.source2 b hb
  · exact JGk_TX2_Lookup04.source2 b hb
  · exact JGk_TX2_Lookup05.source2 b hb
  · exact JGk_TX2_Lookup06.source2 b hb
  · exact JGk_TX2_Lookup07.source2 b hb
  · exact JGk_TX2_Lookup08.source2 b hb
  · exact JGk_TX2_Lookup09.source2 b hb
  · exact JGk_TX2_Lookup10.source2 b hb
  · exact JGk_TX2_Lookup11.source2 b hb
  · exact JGk_TX2_Lookup12.source2 b hb
  · exact JGk_TX2_Lookup13.source2 b hb
  · exact JGk_TX2_Lookup14.source2 b hb
  · exact JGk_TX2_Lookup15.source2 b hb
  · exact JGk_TX2_Lookup16.source2 b hb
  · exact JGk_TX2_Lookup17.source2 b hb
#print axioms source2
theorem frontier0 : OraclePortSelectedDraft.orderedFrontier JGf_TX2_M0Roots.indices=JGk_TX2_Group0_00.stream :=
  JGk_TX2_FrontierOrder0.source
#print axioms frontier0
theorem physical0 (h : Nat) (hh : h<18) (b : Nat) (hb : b ∈ JGf_TX2_M0Roots.bases h) :
    JGh_TX2_NodeViews.readCell JGh_TX2_NodeViews.nodes0
      ((OraclePortSelectedDraft.orderedFrontier JGf_TX2_M0Roots.indices).idxOf (h,b))=JGf_TX2_M0Roots.siblingAt h b := by
  rw [frontier0]
  exact source0 h hh b hb
#print axioms physical0
theorem frontier1 : OraclePortSelectedDraft.orderedFrontier JGh_TX2_M1Roots.indices=JGk_TX2_Group0_00.stream :=
  JGk_TX2_FrontierOrder0.source
#print axioms frontier1
theorem physical1 (h : Nat) (hh : h<18) (b : Nat) (hb : b ∈ JGh_TX2_M1Roots.bases h) :
    JGh_TX2_NodeViews.readCell JGh_TX2_NodeViews.nodes1
      ((OraclePortSelectedDraft.orderedFrontier JGh_TX2_M1Roots.indices).idxOf (h,b))=JGh_TX2_M1Roots.siblingAt h b := by
  rw [frontier1]
  exact source1 h hh b hb
#print axioms physical1
theorem frontier2 : OraclePortSelectedDraft.orderedFrontier JGc_TX2_M2Roots.indices=JGk_TX2_Group2_00.stream :=
  JGk_TX2_FrontierOrder2.source
#print axioms frontier2
theorem physical2 (h : Nat) (hh : h<18) (b : Nat) (hb : b ∈ JGc_TX2_M2Roots.bases h) :
    JGh_TX2_NodeViews.readCell JGh_TX2_NodeViews.nodes2
      ((OraclePortSelectedDraft.orderedFrontier JGc_TX2_M2Roots.indices).idxOf (h,b))=JGc_TX2_M2Roots.siblingAt h b := by
  rw [frontier2]
  exact source2 h hh b hb
#print axioms physical2
end AspisR1.JGk_TX2_SiblingLaws
