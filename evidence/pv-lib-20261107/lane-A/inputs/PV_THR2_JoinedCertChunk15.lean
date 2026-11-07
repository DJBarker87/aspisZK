import PV_THR2_BoxPath443Return
import PV_THR2_BoxPath458Return
import PV_THR2_BoxPath537Return
import PV_THR2_JoinedCertChunk1
import PV_THR2_JoinedCertChunk13
import PV_THR2_JoinedCertChunk14
import PV_THR2_JoinedCertChunk8
import PV_THR2_JoinedCertDecidable
import PV_THR2_JoinedCertDescriptor
import PV_THR2_OperatorCertificatePrefix
import PV_THR2_OperatorRetainedMetadataComposition
import PV_THR2_OwnUniformBeforeCertificate
import PV_THR2_OwnUniformCertificatePrefix
import PV_THR2_OwnUniformMetadataRun
import PV_THR2_OwnUniformReturnCertificate
import PV_THR2_OwnUniformSpawnRun
import PV_THR2_Source166BuilderFull
import PV_THR2_Source166Captures
import PV_THR2_Source166Prologue
import PV_THR2_Source270Captures
import PV_THR2_Source270Prologue

set_option autoImplicit false
noncomputable section
namespace PV_THR2_JoinedCertRegionExtraFrontiers
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_STX2_SliceMachine PV_EVHB_OwnerMachine
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Actual source166/270 chain; its generated sites exclude registration by shape. -/
theorem Source166Prologue {E : Type} (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (q : PV_THR2_IntrinsicState.State OWNER E) :
    PV_THR2_JoinedCertDispatchTrace.Certificate C K P H (PV_THR2_Source166Prologue.steps C q) q :=
  PV_THR2_JoinedCertRegionFrontierCertificate.chain C K P H PV_THR2_Source166Prologue.chain _ _ PV_THR2_Source166Prologue.shape
    (⟨(by intro h; have bad := h.1; cases bad),⟨(by intro h; have bad := h.1; cases bad),⟨(by intro h; have bad := h.1; cases bad),⟨(by intro h; have bad := h.1; cases bad),True.intro⟩⟩⟩⟩) q
#print axioms Source166Prologue
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Actual source166/270 chain; its generated sites exclude registration by shape. -/
theorem Source166Captures {E : Type} (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (q : PV_THR2_IntrinsicState.State OWNER E) :
    PV_THR2_JoinedCertDispatchTrace.Certificate C K P H (PV_THR2_Source166Captures.steps C q) q :=
  PV_THR2_JoinedCertRegionFrontierCertificate.chain C K P H PV_THR2_Source166Captures.chain _ _ PV_THR2_Source166Captures.shape
    (⟨(by intro h; have bad := h.1; cases bad),⟨(by intro h; have bad := h.1; cases bad),True.intro⟩⟩) q
#print axioms Source166Captures
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Actual source166/270 chain; its generated sites exclude registration by shape. -/
theorem Source270Prologue {E : Type} (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (q : PV_THR2_IntrinsicState.State OWNER E) :
    PV_THR2_JoinedCertDispatchTrace.Certificate C K P H (PV_THR2_Source270Prologue.steps C q) q :=
  PV_THR2_JoinedCertRegionFrontierCertificate.chain C K P H PV_THR2_Source270Prologue.chain _ _ PV_THR2_Source270Prologue.shape
    (⟨(by intro h; have bad := h.1; cases bad),⟨(by intro h; have bad := h.1; cases bad),⟨(by intro h; have bad := h.1; cases bad),⟨(by intro h; have bad := h.1; cases bad),⟨(by intro h; have bad := h.1; cases bad),⟨(by intro h; have bad := h.1; cases bad),⟨(by intro h; have bad := h.1; cases bad),⟨(by intro h; have bad := h.1; cases bad),⟨(by intro h; have bad := h.1; cases bad),⟨(by intro h; have bad := h.1; cases bad),⟨(by intro h; have bad := h.1; cases bad),⟨(by intro h; have bad := h.1; cases bad),⟨(by intro h; have bad := h.1; cases bad),⟨(by intro h; have bad := h.1; cases bad),⟨(by intro h; have bad := h.1; cases bad),⟨(by intro h; have bad := h.1; cases bad),True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩) q
#print axioms Source270Prologue
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Actual source166/270 chain; its generated sites exclude registration by shape. -/
theorem Source270Captures {E : Type} (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (q : PV_THR2_IntrinsicState.State OWNER E) :
    PV_THR2_JoinedCertDispatchTrace.Certificate C K P H (PV_THR2_Source270Captures.steps C q) q :=
  PV_THR2_JoinedCertRegionFrontierCertificate.chain C K P H PV_THR2_Source270Captures.chain _ _ PV_THR2_Source270Captures.shape
    (⟨(by intro h; have bad := h.1; cases bad),⟨(by intro h; have bad := h.1; cases bad),True.intro⟩⟩) q
#print axioms Source270Captures
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Actual7916 issuance/full reply; the named original builder child stays arbitrary. -/
theorem Source166BuilderFull {E : Type} (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (q : PV_THR2_IntrinsicState.State OWNER E) :
    PV_THR2_JoinedCertDispatchTrace.Certificate C K P H
      (PV_THR2_Source166BuilderFull.steps C q) q := by
  apply PV_THR2_JoinedCertRegionFrontierCertificate.selected
  intro c w es stack h
  rcases c with ⟨⟨a,rest,loops,wait,unwind,done⟩,parents,s⟩
  rcases h with ⟨rfl,rfl,rfl,rfl⟩
  exact PV_THR2_JoinedCertRegionChildCertificate.run C K P H s a parents loops
    (PV_THR2_F166.live.body.drop 7) PV_THR2_Source166BuilderFull.source.1
    PV_THR2_Source166BuilderFull.source.2.1 PV_THR2_Source166BuilderFull.source.2.2
    [] 4 w es stack rfl (PV_THR2_JoinedCertDispatchIds.by_id _ (by decide) (by decide) (by decide))
#print axioms Source166BuilderFull
end PV_THR2_JoinedCertRegionExtraFrontiers

set_option autoImplicit false
noncomputable section
namespace PV_THR2_JoinedCertRegionSpawnComposition
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_STX2_SliceMachine PV_EVHB_OwnerMachine
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Compose the finite certificates in the exact already proved original segment
order. Source runs are consumed BY NAME; stores, child outcomes and both arms
remain symbolic. This is a prefix certificate, not an OwnInit closure theorem. -/
theorem run {E : Type} (C : Carrier OWNER Data) (K : Control)
    (fallback : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (q : PV_THR2_IntrinsicState.State OWNER E) :
    let P := PV_THR2_Source208Table.table (PV_THR2_Source15Table.resolve (PV_THR2_OwnInitChildren.resolve (PV_THR2_SourceSpawnTable.resolve (PV_THR2_Source270Table.resolve (PV_THR2_Source361Children.resolve (PV_THR2_Source361HookChildren.resolve (PV_THR2_Source361PacketChildren.resolve (PV_THR2_Source361ScopeChildren.resolve (PV_THR2_Source361BoxTable.resolve (PV_THR2_BoxFromTable.resolve (PV_THR2_Source361InitChildren.resolve fallback)))))))))))
    let q0 := q
    let q1 := PV_THR2_Source15ClosureAggregate.after C q0
    let q2 := PV_THR2_Source15SpawnEnter.after C q1
    let q3 := PV_THR2_Source166Prologue.after C q2
    let q4 := PV_THR2_Source166BuilderFull.after C H q3
    let q5 := PV_THR2_Source166Captures.after C q4
    let q6 := PV_THR2_Source166Enter270.after C q5
    let q7 := PV_THR2_Source270Prologue.after C q6
    let q8 := PV_THR2_Source270ScopeArcFull.after C H q7
    let q9 := PV_THR2_Source270ArcStorage.after C q8
    let q10 := PV_THR2_Source270ArcAggregate.after C q9
    let q11 := PV_THR2_Source270Captures.after C q10
    let q12 := PV_THR2_Source270Enter361.after C q11
    let q13 := PV_THR2_Source361Prologue.after C q12
    PV_THR2_JoinedCertDispatchTrace.Certificate C K P H
      ((PV_THR2_Source15ClosureAggregate.steps q0) + ((PV_THR2_Source15SpawnEnter.steps C q1) + ((PV_THR2_Source166Prologue.steps C q2) + ((PV_THR2_Source166BuilderFull.steps C q3) + ((PV_THR2_Source166Captures.steps C q4) + ((PV_THR2_Source166Enter270.steps C q5) + ((PV_THR2_Source270Prologue.steps C q6) + ((PV_THR2_Source270ScopeArcFull.steps C q7) + ((PV_THR2_Source270ArcStorage.steps C q8) + ((PV_THR2_Source270ArcAggregate.steps C q9) + ((PV_THR2_Source270Captures.steps C q10) + ((PV_THR2_Source270Enter361.steps C q11) + ((PV_THR2_Source361Prologue.steps C q12) + ((PV_THR2_Source361FirstAggregate.steps C q13))))))))))))))) q0 := by
  intro P q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13
  apply PV_THR2_JoinedCertDispatchTrace.append C K _ H (PV_THR2_Source15ClosureAggregate.steps q0) ((PV_THR2_Source15SpawnEnter.steps C q1) + ((PV_THR2_Source166Prologue.steps C q2) + ((PV_THR2_Source166BuilderFull.steps C q3) + ((PV_THR2_Source166Captures.steps C q4) + ((PV_THR2_Source166Enter270.steps C q5) + ((PV_THR2_Source270Prologue.steps C q6) + ((PV_THR2_Source270ScopeArcFull.steps C q7) + ((PV_THR2_Source270ArcStorage.steps C q8) + ((PV_THR2_Source270ArcAggregate.steps C q9) + ((PV_THR2_Source270Captures.steps C q10) + ((PV_THR2_Source270Enter361.steps C q11) + ((PV_THR2_Source361Prologue.steps C q12) + ((PV_THR2_Source361FirstAggregate.steps C q13)))))))))))))) _ _ (by rw [PV_THR2_Source15ClosureAggregate.run])
  · exact PV_THR2_JoinedCertRegionOneFrontiers.Source15ClosureAggregate C K _ H _
  · 
    apply PV_THR2_JoinedCertDispatchTrace.append C K _ H (PV_THR2_Source15SpawnEnter.steps C q1) ((PV_THR2_Source166Prologue.steps C q2) + ((PV_THR2_Source166BuilderFull.steps C q3) + ((PV_THR2_Source166Captures.steps C q4) + ((PV_THR2_Source166Enter270.steps C q5) + ((PV_THR2_Source270Prologue.steps C q6) + ((PV_THR2_Source270ScopeArcFull.steps C q7) + ((PV_THR2_Source270ArcStorage.steps C q8) + ((PV_THR2_Source270ArcAggregate.steps C q9) + ((PV_THR2_Source270Captures.steps C q10) + ((PV_THR2_Source270Enter361.steps C q11) + ((PV_THR2_Source361Prologue.steps C q12) + ((PV_THR2_Source361FirstAggregate.steps C q13))))))))))))) _ _ (by rw [PV_THR2_Source15SpawnEnter.run])
    · exact PV_THR2_JoinedCertRegionEntryFrontiers.Source15SpawnEnter C K _ H _
    · 
      apply PV_THR2_JoinedCertDispatchTrace.append C K _ H (PV_THR2_Source166Prologue.steps C q2) ((PV_THR2_Source166BuilderFull.steps C q3) + ((PV_THR2_Source166Captures.steps C q4) + ((PV_THR2_Source166Enter270.steps C q5) + ((PV_THR2_Source270Prologue.steps C q6) + ((PV_THR2_Source270ScopeArcFull.steps C q7) + ((PV_THR2_Source270ArcStorage.steps C q8) + ((PV_THR2_Source270ArcAggregate.steps C q9) + ((PV_THR2_Source270Captures.steps C q10) + ((PV_THR2_Source270Enter361.steps C q11) + ((PV_THR2_Source361Prologue.steps C q12) + ((PV_THR2_Source361FirstAggregate.steps C q13)))))))))))) _ _ (by rw [PV_THR2_Source166Prologue.run])
      · exact PV_THR2_JoinedCertRegionExtraFrontiers.Source166Prologue C K _ H _
      · 
        apply PV_THR2_JoinedCertDispatchTrace.append C K _ H (PV_THR2_Source166BuilderFull.steps C q3) ((PV_THR2_Source166Captures.steps C q4) + ((PV_THR2_Source166Enter270.steps C q5) + ((PV_THR2_Source270Prologue.steps C q6) + ((PV_THR2_Source270ScopeArcFull.steps C q7) + ((PV_THR2_Source270ArcStorage.steps C q8) + ((PV_THR2_Source270ArcAggregate.steps C q9) + ((PV_THR2_Source270Captures.steps C q10) + ((PV_THR2_Source270Enter361.steps C q11) + ((PV_THR2_Source361Prologue.steps C q12) + ((PV_THR2_Source361FirstAggregate.steps C q13))))))))))) _ _ (by rw [PV_THR2_Source166BuilderFull.run])
        · exact PV_THR2_JoinedCertRegionExtraFrontiers.Source166BuilderFull C K _ H _
        · 
          apply PV_THR2_JoinedCertDispatchTrace.append C K _ H (PV_THR2_Source166Captures.steps C q4) ((PV_THR2_Source166Enter270.steps C q5) + ((PV_THR2_Source270Prologue.steps C q6) + ((PV_THR2_Source270ScopeArcFull.steps C q7) + ((PV_THR2_Source270ArcStorage.steps C q8) + ((PV_THR2_Source270ArcAggregate.steps C q9) + ((PV_THR2_Source270Captures.steps C q10) + ((PV_THR2_Source270Enter361.steps C q11) + ((PV_THR2_Source361Prologue.steps C q12) + ((PV_THR2_Source361FirstAggregate.steps C q13)))))))))) _ _ (by rw [PV_THR2_Source166Captures.run])
          · exact PV_THR2_JoinedCertRegionExtraFrontiers.Source166Captures C K _ H _
          · 
            apply PV_THR2_JoinedCertDispatchTrace.append C K _ H (PV_THR2_Source166Enter270.steps C q5) ((PV_THR2_Source270Prologue.steps C q6) + ((PV_THR2_Source270ScopeArcFull.steps C q7) + ((PV_THR2_Source270ArcStorage.steps C q8) + ((PV_THR2_Source270ArcAggregate.steps C q9) + ((PV_THR2_Source270Captures.steps C q10) + ((PV_THR2_Source270Enter361.steps C q11) + ((PV_THR2_Source361Prologue.steps C q12) + ((PV_THR2_Source361FirstAggregate.steps C q13))))))))) _ _ (by rw [PV_THR2_Source166Enter270.run])
            · exact PV_THR2_JoinedCertRegionEntryFrontiers.Source166Enter270 C K _ H _
            · 
              apply PV_THR2_JoinedCertDispatchTrace.append C K _ H (PV_THR2_Source270Prologue.steps C q6) ((PV_THR2_Source270ScopeArcFull.steps C q7) + ((PV_THR2_Source270ArcStorage.steps C q8) + ((PV_THR2_Source270ArcAggregate.steps C q9) + ((PV_THR2_Source270Captures.steps C q10) + ((PV_THR2_Source270Enter361.steps C q11) + ((PV_THR2_Source361Prologue.steps C q12) + ((PV_THR2_Source361FirstAggregate.steps C q13)))))))) _ _ (by rw [PV_THR2_Source270Prologue.run])
              · exact PV_THR2_JoinedCertRegionExtraFrontiers.Source270Prologue C K _ H _
              · 
                apply PV_THR2_JoinedCertDispatchTrace.append C K _ H (PV_THR2_Source270ScopeArcFull.steps C q7) ((PV_THR2_Source270ArcStorage.steps C q8) + ((PV_THR2_Source270ArcAggregate.steps C q9) + ((PV_THR2_Source270Captures.steps C q10) + ((PV_THR2_Source270Enter361.steps C q11) + ((PV_THR2_Source361Prologue.steps C q12) + ((PV_THR2_Source361FirstAggregate.steps C q13))))))) _ _ (by rw [PV_THR2_Source270ScopeArcFull.run])
                · exact PV_THR2_JoinedCertRegionChildFrontiers.Source270ScopeArcFull C K _ H _
                · 
                  apply PV_THR2_JoinedCertDispatchTrace.append C K _ H (PV_THR2_Source270ArcStorage.steps C q8) ((PV_THR2_Source270ArcAggregate.steps C q9) + ((PV_THR2_Source270Captures.steps C q10) + ((PV_THR2_Source270Enter361.steps C q11) + ((PV_THR2_Source361Prologue.steps C q12) + ((PV_THR2_Source361FirstAggregate.steps C q13)))))) _ _ (by rw [PV_THR2_Source270ArcStorage.run])
                  · exact PV_THR2_JoinedCertRegionOneFrontiers.Source270ArcStorage C K _ H _
                  · 
                    apply PV_THR2_JoinedCertDispatchTrace.append C K _ H (PV_THR2_Source270ArcAggregate.steps C q9) ((PV_THR2_Source270Captures.steps C q10) + ((PV_THR2_Source270Enter361.steps C q11) + ((PV_THR2_Source361Prologue.steps C q12) + ((PV_THR2_Source361FirstAggregate.steps C q13))))) _ _ (by rw [PV_THR2_Source270ArcAggregate.run])
                    · exact PV_THR2_JoinedCertRegionOneFrontiers.Source270ArcAggregate C K _ H _
                    · 
                      apply PV_THR2_JoinedCertDispatchTrace.append C K _ H (PV_THR2_Source270Captures.steps C q10) ((PV_THR2_Source270Enter361.steps C q11) + ((PV_THR2_Source361Prologue.steps C q12) + ((PV_THR2_Source361FirstAggregate.steps C q13)))) _ _ (by rw [PV_THR2_Source270Captures.run])
                      · exact PV_THR2_JoinedCertRegionExtraFrontiers.Source270Captures C K _ H _
                      · 
                        apply PV_THR2_JoinedCertDispatchTrace.append C K _ H (PV_THR2_Source270Enter361.steps C q11) ((PV_THR2_Source361Prologue.steps C q12) + ((PV_THR2_Source361FirstAggregate.steps C q13))) _ _ (by rw [PV_THR2_Source270Enter361.run])
                        · exact PV_THR2_JoinedCertRegionEntryFrontiers.Source270Enter361 C K _ H _
                        · 
                          apply PV_THR2_JoinedCertDispatchTrace.append C K _ H (PV_THR2_Source361Prologue.steps C q12) ((PV_THR2_Source361FirstAggregate.steps C q13)) _ _ (by rw [PV_THR2_Source361Prologue.run])
                          · exact PV_THR2_JoinedCertRegionFrontierCertificates.Source361Prologue C K _ H _
                          · exact PV_THR2_JoinedCertRegionOneFrontiers.Source361FirstAggregate C K _ H _
#print axioms run
end PV_THR2_JoinedCertRegionSpawnComposition

set_option autoImplicit false
noncomputable section
namespace PV_THR2_JoinedCertRegionMetadataBeforePacket
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
/-- Conditional on amended-translator acceptance. Exact retarget of the
existing metadata region order through ready drop58, BEFORE changed12801.
No child at12801 is certified neutral; its executed constructor is exceptional.
All source boundaries, stores and arbitrary FULL replies are retained. -/
theorem run {E : Type} (C : Carrier OWNER Data) (K : Control)
    (fallback : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (q : PV_THR2_IntrinsicState.State OWNER E) :
    let P := PV_THR2_Source208Table.table (PV_THR2_Source15Table.resolve (PV_THR2_OwnInitChildren.resolve (PV_THR2_SourceSpawnTable.resolve (PV_THR2_Source270Table.resolve (PV_THR2_Source361Children.resolve (PV_THR2_Source361HookChildren.resolve (PV_THR2_Source361PacketChildren.resolve (PV_THR2_Source361ScopeChildren.resolve (PV_THR2_Source361BoxTable.resolve (PV_THR2_BoxFromTable.resolve (PV_THR2_Source361InitChildren.resolve fallback)))))))))))
    let q0 := q
    let q1 := PV_THR2_Source361Full23.after C H q0
    let q2 := PV_THR2_Source361Chain24To27.after C q1
    let q3 := PV_THR2_Source361Full27.after C H q2
    let q4 := PV_THR2_Source361Chain28To34.after C q3
    let q5 := PV_THR2_Source361Full34.after C H q4
    let q6 := PV_THR2_Source361Chain35To40.after C q5
    let q7 := PV_THR2_Source361HookBranch.after C q6
    let q8 := PV_THR2_Source361HookTrueFull.after C H q7
    let q9 := PV_THR2_Source361HookFalsePrefix.after C q8
    let q10 := PV_THR2_Source361HookFalseFull.after C H q9
    let q11 := PV_THR2_Source361HookTrueSuffix.after C q10
    let q12 := PV_THR2_Source361HookFalseSuffix.after C q11
    let q13 := PV_THR2_Source361Chain41To49.after C q12
    let q14 := PV_THR2_Source361Aggregate49.after C q13
    let q15 := PV_THR2_Source361Full50.after C H q14
    let q16 := PV_THR2_Source361Chain51To53.after C q15
    let q17 := PV_THR2_Source361Aggregate53.after C q16
    let q18 := PV_THR2_Source361Aggregate54.after C q17
    let q19 := PV_THR2_Source361Chain55To58.after C q18
    PV_THR2_JoinedCertDispatchTrace.Certificate C K P H ((PV_THR2_Source361Full23.steps C q0) + ((PV_THR2_Source361Chain24To27.steps C q1) + ((PV_THR2_Source361Full27.steps C q2) + ((PV_THR2_Source361Chain28To34.steps C q3) + ((PV_THR2_Source361Full34.steps C q4) + ((PV_THR2_Source361Chain35To40.steps C q5) + ((PV_THR2_Source361HookBranch.steps C q6) + ((PV_THR2_Source361HookTrueFull.steps C q7) + ((PV_THR2_Source361HookFalsePrefix.steps C q8) + ((PV_THR2_Source361HookFalseFull.steps C q9) + ((PV_THR2_Source361HookTrueSuffix.steps C q10) + ((PV_THR2_Source361HookFalseSuffix.steps C q11) + ((PV_THR2_Source361Chain41To49.steps C q12) + ((PV_THR2_Source361Aggregate49.steps C q13) + ((PV_THR2_Source361Full50.steps C q14) + ((PV_THR2_Source361Chain51To53.steps C q15) + ((PV_THR2_Source361Aggregate53.steps C q16) + ((PV_THR2_Source361Aggregate54.steps C q17) + (PV_THR2_Source361Chain55To58.steps C q18))))))))))))))))))) q0 := by
  intro P q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19
  apply PV_THR2_JoinedCertDispatchTrace.append C K P H (PV_THR2_Source361Full23.steps C q0) ((PV_THR2_Source361Chain24To27.steps C q1) + ((PV_THR2_Source361Full27.steps C q2) + ((PV_THR2_Source361Chain28To34.steps C q3) + ((PV_THR2_Source361Full34.steps C q4) + ((PV_THR2_Source361Chain35To40.steps C q5) + ((PV_THR2_Source361HookBranch.steps C q6) + ((PV_THR2_Source361HookTrueFull.steps C q7) + ((PV_THR2_Source361HookFalsePrefix.steps C q8) + ((PV_THR2_Source361HookFalseFull.steps C q9) + ((PV_THR2_Source361HookTrueSuffix.steps C q10) + ((PV_THR2_Source361HookFalseSuffix.steps C q11) + ((PV_THR2_Source361Chain41To49.steps C q12) + ((PV_THR2_Source361Aggregate49.steps C q13) + ((PV_THR2_Source361Full50.steps C q14) + ((PV_THR2_Source361Chain51To53.steps C q15) + ((PV_THR2_Source361Aggregate53.steps C q16) + ((PV_THR2_Source361Aggregate54.steps C q17) + (PV_THR2_Source361Chain55To58.steps C q18)))))))))))))))))) _ _ (by rw [PV_THR2_Source361Full23.run])
  · exact PV_THR2_JoinedCertRegionChildFrontiers.Source361Full23 C K P H _
  ·
    apply PV_THR2_JoinedCertDispatchTrace.append C K P H (PV_THR2_Source361Chain24To27.steps C q1) ((PV_THR2_Source361Full27.steps C q2) + ((PV_THR2_Source361Chain28To34.steps C q3) + ((PV_THR2_Source361Full34.steps C q4) + ((PV_THR2_Source361Chain35To40.steps C q5) + ((PV_THR2_Source361HookBranch.steps C q6) + ((PV_THR2_Source361HookTrueFull.steps C q7) + ((PV_THR2_Source361HookFalsePrefix.steps C q8) + ((PV_THR2_Source361HookFalseFull.steps C q9) + ((PV_THR2_Source361HookTrueSuffix.steps C q10) + ((PV_THR2_Source361HookFalseSuffix.steps C q11) + ((PV_THR2_Source361Chain41To49.steps C q12) + ((PV_THR2_Source361Aggregate49.steps C q13) + ((PV_THR2_Source361Full50.steps C q14) + ((PV_THR2_Source361Chain51To53.steps C q15) + ((PV_THR2_Source361Aggregate53.steps C q16) + ((PV_THR2_Source361Aggregate54.steps C q17) + (PV_THR2_Source361Chain55To58.steps C q18))))))))))))))))) _ _ (by rw [PV_THR2_Source361Chain24To27.run])
    · exact PV_THR2_JoinedCertRegionFrontierCertificates.Source361Chain24To27 C K P H _
    ·
      apply PV_THR2_JoinedCertDispatchTrace.append C K P H (PV_THR2_Source361Full27.steps C q2) ((PV_THR2_Source361Chain28To34.steps C q3) + ((PV_THR2_Source361Full34.steps C q4) + ((PV_THR2_Source361Chain35To40.steps C q5) + ((PV_THR2_Source361HookBranch.steps C q6) + ((PV_THR2_Source361HookTrueFull.steps C q7) + ((PV_THR2_Source361HookFalsePrefix.steps C q8) + ((PV_THR2_Source361HookFalseFull.steps C q9) + ((PV_THR2_Source361HookTrueSuffix.steps C q10) + ((PV_THR2_Source361HookFalseSuffix.steps C q11) + ((PV_THR2_Source361Chain41To49.steps C q12) + ((PV_THR2_Source361Aggregate49.steps C q13) + ((PV_THR2_Source361Full50.steps C q14) + ((PV_THR2_Source361Chain51To53.steps C q15) + ((PV_THR2_Source361Aggregate53.steps C q16) + ((PV_THR2_Source361Aggregate54.steps C q17) + (PV_THR2_Source361Chain55To58.steps C q18)))))))))))))))) _ _ (by rw [PV_THR2_Source361Full27.run])
      · exact PV_THR2_JoinedCertRegionChildFrontiers.Source361Full27 C K P H _
      ·
        apply PV_THR2_JoinedCertDispatchTrace.append C K P H (PV_THR2_Source361Chain28To34.steps C q3) ((PV_THR2_Source361Full34.steps C q4) + ((PV_THR2_Source361Chain35To40.steps C q5) + ((PV_THR2_Source361HookBranch.steps C q6) + ((PV_THR2_Source361HookTrueFull.steps C q7) + ((PV_THR2_Source361HookFalsePrefix.steps C q8) + ((PV_THR2_Source361HookFalseFull.steps C q9) + ((PV_THR2_Source361HookTrueSuffix.steps C q10) + ((PV_THR2_Source361HookFalseSuffix.steps C q11) + ((PV_THR2_Source361Chain41To49.steps C q12) + ((PV_THR2_Source361Aggregate49.steps C q13) + ((PV_THR2_Source361Full50.steps C q14) + ((PV_THR2_Source361Chain51To53.steps C q15) + ((PV_THR2_Source361Aggregate53.steps C q16) + ((PV_THR2_Source361Aggregate54.steps C q17) + (PV_THR2_Source361Chain55To58.steps C q18))))))))))))))) _ _ (by rw [PV_THR2_Source361Chain28To34.run])
        · exact PV_THR2_JoinedCertRegionFrontierCertificates.Source361Chain28To34 C K P H _
        ·
          apply PV_THR2_JoinedCertDispatchTrace.append C K P H (PV_THR2_Source361Full34.steps C q4) ((PV_THR2_Source361Chain35To40.steps C q5) + ((PV_THR2_Source361HookBranch.steps C q6) + ((PV_THR2_Source361HookTrueFull.steps C q7) + ((PV_THR2_Source361HookFalsePrefix.steps C q8) + ((PV_THR2_Source361HookFalseFull.steps C q9) + ((PV_THR2_Source361HookTrueSuffix.steps C q10) + ((PV_THR2_Source361HookFalseSuffix.steps C q11) + ((PV_THR2_Source361Chain41To49.steps C q12) + ((PV_THR2_Source361Aggregate49.steps C q13) + ((PV_THR2_Source361Full50.steps C q14) + ((PV_THR2_Source361Chain51To53.steps C q15) + ((PV_THR2_Source361Aggregate53.steps C q16) + ((PV_THR2_Source361Aggregate54.steps C q17) + (PV_THR2_Source361Chain55To58.steps C q18)))))))))))))) _ _ (by rw [PV_THR2_Source361Full34.run])
          · exact PV_THR2_JoinedCertRegionChildFrontiers.Source361Full34 C K P H _
          ·
            apply PV_THR2_JoinedCertDispatchTrace.append C K P H (PV_THR2_Source361Chain35To40.steps C q5) ((PV_THR2_Source361HookBranch.steps C q6) + ((PV_THR2_Source361HookTrueFull.steps C q7) + ((PV_THR2_Source361HookFalsePrefix.steps C q8) + ((PV_THR2_Source361HookFalseFull.steps C q9) + ((PV_THR2_Source361HookTrueSuffix.steps C q10) + ((PV_THR2_Source361HookFalseSuffix.steps C q11) + ((PV_THR2_Source361Chain41To49.steps C q12) + ((PV_THR2_Source361Aggregate49.steps C q13) + ((PV_THR2_Source361Full50.steps C q14) + ((PV_THR2_Source361Chain51To53.steps C q15) + ((PV_THR2_Source361Aggregate53.steps C q16) + ((PV_THR2_Source361Aggregate54.steps C q17) + (PV_THR2_Source361Chain55To58.steps C q18))))))))))))) _ _ (by rw [PV_THR2_Source361Chain35To40.run])
            · exact PV_THR2_JoinedCertRegionFrontierCertificates.Source361Chain35To40 C K P H _
            ·
              apply PV_THR2_JoinedCertDispatchTrace.append C K P H (PV_THR2_Source361HookBranch.steps C q6) ((PV_THR2_Source361HookTrueFull.steps C q7) + ((PV_THR2_Source361HookFalsePrefix.steps C q8) + ((PV_THR2_Source361HookFalseFull.steps C q9) + ((PV_THR2_Source361HookTrueSuffix.steps C q10) + ((PV_THR2_Source361HookFalseSuffix.steps C q11) + ((PV_THR2_Source361Chain41To49.steps C q12) + ((PV_THR2_Source361Aggregate49.steps C q13) + ((PV_THR2_Source361Full50.steps C q14) + ((PV_THR2_Source361Chain51To53.steps C q15) + ((PV_THR2_Source361Aggregate53.steps C q16) + ((PV_THR2_Source361Aggregate54.steps C q17) + (PV_THR2_Source361Chain55To58.steps C q18)))))))))))) _ _ (by rw [PV_THR2_Source361HookBranch.run])
              · exact PV_THR2_JoinedCertRegionOneFrontiers.Source361HookBranch C K P H _
              ·
                apply PV_THR2_JoinedCertDispatchTrace.append C K P H (PV_THR2_Source361HookTrueFull.steps C q7) ((PV_THR2_Source361HookFalsePrefix.steps C q8) + ((PV_THR2_Source361HookFalseFull.steps C q9) + ((PV_THR2_Source361HookTrueSuffix.steps C q10) + ((PV_THR2_Source361HookFalseSuffix.steps C q11) + ((PV_THR2_Source361Chain41To49.steps C q12) + ((PV_THR2_Source361Aggregate49.steps C q13) + ((PV_THR2_Source361Full50.steps C q14) + ((PV_THR2_Source361Chain51To53.steps C q15) + ((PV_THR2_Source361Aggregate53.steps C q16) + ((PV_THR2_Source361Aggregate54.steps C q17) + (PV_THR2_Source361Chain55To58.steps C q18))))))))))) _ _ (by rw [PV_THR2_Source361HookTrueFull.run])
                · exact PV_THR2_JoinedCertRegionChildFrontiers.Source361HookTrueFull C K P H _
                ·
                  apply PV_THR2_JoinedCertDispatchTrace.append C K P H (PV_THR2_Source361HookFalsePrefix.steps C q8) ((PV_THR2_Source361HookFalseFull.steps C q9) + ((PV_THR2_Source361HookTrueSuffix.steps C q10) + ((PV_THR2_Source361HookFalseSuffix.steps C q11) + ((PV_THR2_Source361Chain41To49.steps C q12) + ((PV_THR2_Source361Aggregate49.steps C q13) + ((PV_THR2_Source361Full50.steps C q14) + ((PV_THR2_Source361Chain51To53.steps C q15) + ((PV_THR2_Source361Aggregate53.steps C q16) + ((PV_THR2_Source361Aggregate54.steps C q17) + (PV_THR2_Source361Chain55To58.steps C q18)))))))))) _ _ (by rw [PV_THR2_Source361HookFalsePrefix.run])
                  · exact PV_THR2_JoinedCertRegionFrontierCertificates.Source361HookFalsePrefix C K P H _
                  ·
                    apply PV_THR2_JoinedCertDispatchTrace.append C K P H (PV_THR2_Source361HookFalseFull.steps C q9) ((PV_THR2_Source361HookTrueSuffix.steps C q10) + ((PV_THR2_Source361HookFalseSuffix.steps C q11) + ((PV_THR2_Source361Chain41To49.steps C q12) + ((PV_THR2_Source361Aggregate49.steps C q13) + ((PV_THR2_Source361Full50.steps C q14) + ((PV_THR2_Source361Chain51To53.steps C q15) + ((PV_THR2_Source361Aggregate53.steps C q16) + ((PV_THR2_Source361Aggregate54.steps C q17) + (PV_THR2_Source361Chain55To58.steps C q18))))))))) _ _ (by rw [PV_THR2_Source361HookFalseFull.run])
                    · exact PV_THR2_JoinedCertRegionChildFrontiers.Source361HookFalseFull C K P H _
                    ·
                      apply PV_THR2_JoinedCertDispatchTrace.append C K P H (PV_THR2_Source361HookTrueSuffix.steps C q10) ((PV_THR2_Source361HookFalseSuffix.steps C q11) + ((PV_THR2_Source361Chain41To49.steps C q12) + ((PV_THR2_Source361Aggregate49.steps C q13) + ((PV_THR2_Source361Full50.steps C q14) + ((PV_THR2_Source361Chain51To53.steps C q15) + ((PV_THR2_Source361Aggregate53.steps C q16) + ((PV_THR2_Source361Aggregate54.steps C q17) + (PV_THR2_Source361Chain55To58.steps C q18)))))))) _ _ (by rw [PV_THR2_Source361HookTrueSuffix.run])
                      · exact PV_THR2_JoinedCertRegionFrontierCertificates.Source361HookTrueSuffix C K P H _
                      ·
                        apply PV_THR2_JoinedCertDispatchTrace.append C K P H (PV_THR2_Source361HookFalseSuffix.steps C q11) ((PV_THR2_Source361Chain41To49.steps C q12) + ((PV_THR2_Source361Aggregate49.steps C q13) + ((PV_THR2_Source361Full50.steps C q14) + ((PV_THR2_Source361Chain51To53.steps C q15) + ((PV_THR2_Source361Aggregate53.steps C q16) + ((PV_THR2_Source361Aggregate54.steps C q17) + (PV_THR2_Source361Chain55To58.steps C q18))))))) _ _ (by rw [PV_THR2_Source361HookFalseSuffix.run])
                        · exact PV_THR2_JoinedCertRegionFrontierCertificates.Source361HookFalseSuffix C K P H _
                        ·
                          apply PV_THR2_JoinedCertDispatchTrace.append C K P H (PV_THR2_Source361Chain41To49.steps C q12) ((PV_THR2_Source361Aggregate49.steps C q13) + ((PV_THR2_Source361Full50.steps C q14) + ((PV_THR2_Source361Chain51To53.steps C q15) + ((PV_THR2_Source361Aggregate53.steps C q16) + ((PV_THR2_Source361Aggregate54.steps C q17) + (PV_THR2_Source361Chain55To58.steps C q18)))))) _ _ (by rw [PV_THR2_Source361Chain41To49.run])
                          · exact PV_THR2_JoinedCertRegionFrontierCertificates.Source361Chain41To49 C K P H _
                          ·
                            apply PV_THR2_JoinedCertDispatchTrace.append C K P H (PV_THR2_Source361Aggregate49.steps C q13) ((PV_THR2_Source361Full50.steps C q14) + ((PV_THR2_Source361Chain51To53.steps C q15) + ((PV_THR2_Source361Aggregate53.steps C q16) + ((PV_THR2_Source361Aggregate54.steps C q17) + (PV_THR2_Source361Chain55To58.steps C q18))))) _ _ (by rw [PV_THR2_Source361Aggregate49.run])
                            · exact PV_THR2_JoinedCertRegionOneFrontiers.Source361Aggregate49 C K P H _
                            ·
                              apply PV_THR2_JoinedCertDispatchTrace.append C K P H (PV_THR2_Source361Full50.steps C q14) ((PV_THR2_Source361Chain51To53.steps C q15) + ((PV_THR2_Source361Aggregate53.steps C q16) + ((PV_THR2_Source361Aggregate54.steps C q17) + (PV_THR2_Source361Chain55To58.steps C q18)))) _ _ (by rw [PV_THR2_Source361Full50.run])
                              · exact PV_THR2_JoinedCertRegionChildFrontiers.Source361Full50 C K P H _
                              ·
                                apply PV_THR2_JoinedCertDispatchTrace.append C K P H (PV_THR2_Source361Chain51To53.steps C q15) ((PV_THR2_Source361Aggregate53.steps C q16) + ((PV_THR2_Source361Aggregate54.steps C q17) + (PV_THR2_Source361Chain55To58.steps C q18))) _ _ (by rw [PV_THR2_Source361Chain51To53.run])
                                · exact PV_THR2_JoinedCertRegionFrontierCertificates.Source361Chain51To53 C K P H _
                                ·
                                  apply PV_THR2_JoinedCertDispatchTrace.append C K P H (PV_THR2_Source361Aggregate53.steps C q16) ((PV_THR2_Source361Aggregate54.steps C q17) + (PV_THR2_Source361Chain55To58.steps C q18)) _ _ (by rw [PV_THR2_Source361Aggregate53.run])
                                  · exact PV_THR2_JoinedCertRegionOneFrontiers.Source361Aggregate53 C K P H _
                                  ·
                                    apply PV_THR2_JoinedCertDispatchTrace.append C K P H (PV_THR2_Source361Aggregate54.steps C q17) (PV_THR2_Source361Chain55To58.steps C q18) _ _ (by rw [PV_THR2_Source361Aggregate54.run])
                                    · exact PV_THR2_JoinedCertRegionOneFrontiers.Source361Aggregate54 C K P H _
                                    ·
                                      exact PV_THR2_JoinedCertRegionFrontierCertificates.Source361Chain55To58 C K P H _
#print axioms run
end PV_THR2_JoinedCertRegionMetadataBeforePacket

set_option autoImplicit false
noncomputable section
namespace PV_THR2_JoinedCertRegionMetadataPrefix
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
/-- Exact retained source cost before12801; no operand or store evaluation. -/
def steps {E : Type} (C : Carrier OWNER Data) (K : Control)
    (fallback : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (q : PV_THR2_IntrinsicState.State OWNER E) : Nat :=
    let q0 := q
    let q1 := PV_THR2_Source361Full23.after C H q0
    let q2 := PV_THR2_Source361Chain24To27.after C q1
    let q3 := PV_THR2_Source361Full27.after C H q2
    let q4 := PV_THR2_Source361Chain28To34.after C q3
    let q5 := PV_THR2_Source361Full34.after C H q4
    let q6 := PV_THR2_Source361Chain35To40.after C q5
    let q7 := PV_THR2_Source361HookBranch.after C q6
    let q8 := PV_THR2_Source361HookTrueFull.after C H q7
    let q9 := PV_THR2_Source361HookFalsePrefix.after C q8
    let q10 := PV_THR2_Source361HookFalseFull.after C H q9
    let q11 := PV_THR2_Source361HookTrueSuffix.after C q10
    let q12 := PV_THR2_Source361HookFalseSuffix.after C q11
    let q13 := PV_THR2_Source361Chain41To49.after C q12
    let q14 := PV_THR2_Source361Aggregate49.after C q13
    let q15 := PV_THR2_Source361Full50.after C H q14
    let q16 := PV_THR2_Source361Chain51To53.after C q15
    let q17 := PV_THR2_Source361Aggregate53.after C q16
    let q18 := PV_THR2_Source361Aggregate54.after C q17
    let q19 := PV_THR2_Source361Chain55To58.after C q18
    ((PV_THR2_Source361Full23.steps C q0) + ((PV_THR2_Source361Chain24To27.steps C q1) + ((PV_THR2_Source361Full27.steps C q2) + ((PV_THR2_Source361Chain28To34.steps C q3) + ((PV_THR2_Source361Full34.steps C q4) + ((PV_THR2_Source361Chain35To40.steps C q5) + ((PV_THR2_Source361HookBranch.steps C q6) + ((PV_THR2_Source361HookTrueFull.steps C q7) + ((PV_THR2_Source361HookFalsePrefix.steps C q8) + ((PV_THR2_Source361HookFalseFull.steps C q9) + ((PV_THR2_Source361HookTrueSuffix.steps C q10) + ((PV_THR2_Source361HookFalseSuffix.steps C q11) + ((PV_THR2_Source361Chain41To49.steps C q12) + ((PV_THR2_Source361Aggregate49.steps C q13) + ((PV_THR2_Source361Full50.steps C q14) + ((PV_THR2_Source361Chain51To53.steps C q15) + ((PV_THR2_Source361Aggregate53.steps C q16) + ((PV_THR2_Source361Aggregate54.steps C q17) + (PV_THR2_Source361Chain55To58.steps C q18)))))))))))))))))))
/-- Same source-selected state before12801; the changed call is not consumed. -/
def after {E : Type} (C : Carrier OWNER Data) (K : Control)
    (fallback : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (q : PV_THR2_IntrinsicState.State OWNER E) : PV_THR2_IntrinsicState.State OWNER E :=
    let q0 := q
    let q1 := PV_THR2_Source361Full23.after C H q0
    let q2 := PV_THR2_Source361Chain24To27.after C q1
    let q3 := PV_THR2_Source361Full27.after C H q2
    let q4 := PV_THR2_Source361Chain28To34.after C q3
    let q5 := PV_THR2_Source361Full34.after C H q4
    let q6 := PV_THR2_Source361Chain35To40.after C q5
    let q7 := PV_THR2_Source361HookBranch.after C q6
    let q8 := PV_THR2_Source361HookTrueFull.after C H q7
    let q9 := PV_THR2_Source361HookFalsePrefix.after C q8
    let q10 := PV_THR2_Source361HookFalseFull.after C H q9
    let q11 := PV_THR2_Source361HookTrueSuffix.after C q10
    let q12 := PV_THR2_Source361HookFalseSuffix.after C q11
    let q13 := PV_THR2_Source361Chain41To49.after C q12
    let q14 := PV_THR2_Source361Aggregate49.after C q13
    let q15 := PV_THR2_Source361Full50.after C H q14
    let q16 := PV_THR2_Source361Chain51To53.after C q15
    let q17 := PV_THR2_Source361Aggregate53.after C q16
    let q18 := PV_THR2_Source361Aggregate54.after C q17
    let q19 := PV_THR2_Source361Chain55To58.after C q18
    q19
/-- Conditional on amended-translator acceptance. Consume each existing
source segment BY NAME, stopping before the Packet constructor exception. -/
theorem source {E : Type} (C : Carrier OWNER Data) (K : Control)
    (fallback : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (q : PV_THR2_IntrinsicState.State OWNER E) :
    let P := PV_THR2_Source208Table.table (PV_THR2_Source15Table.resolve (PV_THR2_OwnInitChildren.resolve (PV_THR2_SourceSpawnTable.resolve (PV_THR2_Source270Table.resolve (PV_THR2_Source361Children.resolve (PV_THR2_Source361HookChildren.resolve (PV_THR2_Source361PacketChildren.resolve (PV_THR2_Source361ScopeChildren.resolve (PV_THR2_Source361BoxTable.resolve (PV_THR2_BoxFromTable.resolve (PV_THR2_Source361InitChildren.resolve fallback)))))))))))
    PV_THR2_IntrinsicState.advance C K P H (steps C K fallback H q) q =
      after C K fallback H q := by
  intro P
  unfold steps after
  rw [PV_THR2_IntrinsicComposition.advance_add,PV_THR2_Source361Full23.run]
  rw [PV_THR2_IntrinsicComposition.advance_add,PV_THR2_Source361Chain24To27.run]
  rw [PV_THR2_IntrinsicComposition.advance_add,PV_THR2_Source361Full27.run]
  rw [PV_THR2_IntrinsicComposition.advance_add,PV_THR2_Source361Chain28To34.run]
  rw [PV_THR2_IntrinsicComposition.advance_add,PV_THR2_Source361Full34.run]
  rw [PV_THR2_IntrinsicComposition.advance_add,PV_THR2_Source361Chain35To40.run]
  rw [PV_THR2_IntrinsicComposition.advance_add,PV_THR2_Source361HookBranch.run]
  rw [PV_THR2_IntrinsicComposition.advance_add,PV_THR2_Source361HookTrueFull.run]
  rw [PV_THR2_IntrinsicComposition.advance_add,PV_THR2_Source361HookFalsePrefix.run]
  rw [PV_THR2_IntrinsicComposition.advance_add,PV_THR2_Source361HookFalseFull.run]
  rw [PV_THR2_IntrinsicComposition.advance_add,PV_THR2_Source361HookTrueSuffix.run]
  rw [PV_THR2_IntrinsicComposition.advance_add,PV_THR2_Source361HookFalseSuffix.run]
  rw [PV_THR2_IntrinsicComposition.advance_add,PV_THR2_Source361Chain41To49.run]
  rw [PV_THR2_IntrinsicComposition.advance_add,PV_THR2_Source361Aggregate49.run]
  rw [PV_THR2_IntrinsicComposition.advance_add,PV_THR2_Source361Full50.run]
  rw [PV_THR2_IntrinsicComposition.advance_add,PV_THR2_Source361Chain51To53.run]
  rw [PV_THR2_IntrinsicComposition.advance_add,PV_THR2_Source361Aggregate53.run]
  rw [PV_THR2_IntrinsicComposition.advance_add,PV_THR2_Source361Aggregate54.run]
  exact PV_THR2_Source361Chain55To58.run C K P H _
#print axioms source
/-- Retargeted D775 Packet certificate, not a source execution premise. -/
theorem packet {E : Type} (C : Carrier OWNER Data) (K : Control)
    (fallback : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (q : PV_THR2_IntrinsicState.State OWNER E) :
    let P := PV_THR2_Source208Table.table (PV_THR2_Source15Table.resolve (PV_THR2_OwnInitChildren.resolve (PV_THR2_SourceSpawnTable.resolve (PV_THR2_Source270Table.resolve (PV_THR2_Source361Children.resolve (PV_THR2_Source361HookChildren.resolve (PV_THR2_Source361PacketChildren.resolve (PV_THR2_Source361ScopeChildren.resolve (PV_THR2_Source361BoxTable.resolve (PV_THR2_BoxFromTable.resolve (PV_THR2_Source361InitChildren.resolve fallback)))))))))))
    PV_THR2_JoinedCertDispatchTrace.Certificate C K P H (steps C K fallback H q) q :=
  PV_THR2_JoinedCertRegionMetadataBeforePacket.run C K fallback H q
#print axioms packet
/-- The retained full D775 metadata group extends this prefix symbolically. -/
theorem bound {E : Type} (C : Carrier OWNER Data) (K : Control)
    (fallback : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (q : PV_THR2_IntrinsicState.State OWNER E) :
    steps C K fallback H q ≤ PV_THR2_OwnUniformMetadataRun.steps C K fallback H q := by
  unfold steps PV_THR2_OwnUniformMetadataRun.steps
  apply Nat.add_le_add_left
  apply Nat.add_le_add_left
  apply Nat.add_le_add_left
  apply Nat.add_le_add_left
  apply Nat.add_le_add_left
  apply Nat.add_le_add_left
  apply Nat.add_le_add_left
  apply Nat.add_le_add_left
  apply Nat.add_le_add_left
  apply Nat.add_le_add_left
  apply Nat.add_le_add_left
  apply Nat.add_le_add_left
  apply Nat.add_le_add_left
  apply Nat.add_le_add_left
  apply Nat.add_le_add_left
  apply Nat.add_le_add_left
  apply Nat.add_le_add_left
  apply Nat.add_le_add_left
  exact Nat.le_add_right _ _
#print axioms bound
/-- Consume the cached OWNER certificate BY NAME at the exact shorter fuel. -/
theorem owner {E : Type} (C : Carrier OWNER Data) (K : Control)
    (fallback : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (q : PV_THR2_IntrinsicState.State OWNER E) :
    let P := PV_THR2_Source208Table.table (PV_THR2_Source15Table.resolve (PV_THR2_OwnInitChildren.resolve (PV_THR2_SourceSpawnTable.resolve (PV_THR2_Source270Table.resolve (PV_THR2_Source361Children.resolve (PV_THR2_Source361HookChildren.resolve (PV_THR2_Source361PacketChildren.resolve (PV_THR2_Source361ScopeChildren.resolve (PV_THR2_Source361BoxTable.resolve (PV_THR2_BoxFromTable.resolve (PV_THR2_Source361InitChildren.resolve fallback)))))))))))
    PV_THR2_OwnUniformBeforeCertificate.Certificate C K P H (steps C K fallback H q) q :=
  PV_THR2_OwnUniformCertificatePrefix.take C K _ H
    (PV_THR2_OwnUniformMetadataComposition.run C K fallback H q)
    _ (bound C K fallback H q)
#print axioms owner
/-- Consume the cached operator certificate BY NAME, without re-proving it. -/
theorem operators {E : Type} (C : Carrier OWNER Data) (K : Control)
    (fallback : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (q : PV_THR2_IntrinsicState.State OWNER E) :
    let P := PV_THR2_Source208Table.table (PV_THR2_Source15Table.resolve (PV_THR2_OwnInitChildren.resolve (PV_THR2_SourceSpawnTable.resolve (PV_THR2_Source270Table.resolve (PV_THR2_Source361Children.resolve (PV_THR2_Source361HookChildren.resolve (PV_THR2_Source361PacketChildren.resolve (PV_THR2_Source361ScopeChildren.resolve (PV_THR2_Source361BoxTable.resolve (PV_THR2_BoxFromTable.resolve (PV_THR2_Source361InitChildren.resolve fallback)))))))))))
    PV_THR2_OperatorInstalledCertificate.Certificate C K P H
      (steps (PV_THR2_OperatorCarrier.carrier C) K fallback H q) q :=
  PV_THR2_OperatorCertificatePrefix.take C K _ H
    (PV_THR2_OperatorRetainedMetadataComposition.run C K fallback H q)
    _ (bound (PV_THR2_OperatorCarrier.carrier C) K fallback H q)
#print axioms operators
end PV_THR2_JoinedCertRegionMetadataPrefix

set_option autoImplicit false
noncomputable section
namespace PV_THR2_JoinedCertRegionOriginalBefore12801
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
open PV_THR2_CatchOriginalClassified
/-- Conditional on amended-translator acceptance. Verbatim original source
cases; combine RETARGETED D775 certificates at named original boundaries.
The prefix ends before changed12801. No resolver lift is applied here, no source
execution is re-proved, and no exclusion/receiver/read/root premise is added. -/
theorem run {E : Type} (base : Carrier OWNER Data) (ctl : Control)
    (fallback : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (s : Store Data) (n : Nat) (f : Data) (b : Bool) (input mapValue value result : Data) (w : OWNER)
    (key : (PV_THR2_RunEntryReturned.keyReply (PV_THR2_FnOnceDispatch.handler handler) s n f b w).answer = .returned (.ok input))
    (mapped : (PV_THR2_RunEntryNext.mapReply (PV_THR2_FnOnceDispatch.handler handler) s n f b input w).answer = .returned (.ok mapValue))
    (error : (PV_THR2_RunEntryErrorReply.errorReply (PV_THR2_FnOnceDispatch.handler handler) s n f b input mapValue w).answer = .returned (.ok value))
    (branch : (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_FnOnceDispatch.handler handler) s n f b input mapValue value w).answer = .returned (.ok result))
    (variant : (PV_THR2_ThreadFields.control ctl).variant result = some 0)
    (actual : Data) (p : Address) (output : Data)
    (field : (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier (PV_THR2_RangeLiterals.carrier base))) b).field result 0 = some actual)
    (address : (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier (PV_THR2_RangeLiterals.carrier base))) b).dereference
      (PV_THR2_WrapRunEntryBranchReply.branchReply (PV_THR2_FnOnceDispatch.handler handler)
        s n f b input mapValue value w).world actual = some p)
    (callback : (PV_THR2_WrapRunEntryCallbackReturned.reply handler s n f b input mapValue value result actual p w).answer =
      .returned (.ok output))
    (inactive : (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier (PV_THR2_RangeLiterals.carrier base))) b).truth output = some false)
    (tlsValue : Data)
    (tls : (PV_THR2_WrapRunEntryActiveChild.reply handler s n f b input mapValue value result actual p output w).answer = .returned (.ok tlsValue))
    (counter : Data)
    (counterReturned : (PV_THR2_ScopeReply121.reply (PV_THR2_FnOnceDispatch.handler handler)
      (PV_THR2_WrapRunEntryScopePrefix.atPrologue s n f b input mapValue value result actual p output tlsValue).store
      (PV_THR2_WrapRunEntryActiveChild.reply handler s n f b input mapValue value result actual p output w).world).answer = .returned (.ok counter))
    (thread : Data)
    (threadReturned : (PV_THR2_ScopeOriginalReturned122.reply handler s n f b input mapValue value result actual p output tlsValue counter w).answer = .returned (.ok thread))
    (panicked : Data)
    (panickedReturned : (PV_THR2_ScopeOriginalReturned123.reply handler s n f b input mapValue value result actual p output tlsValue counter thread w).answer = .returned (.ok panicked))
    (arc : Data)
    (arcReturned : (PV_THR2_ScopeOriginalArcReturned.reply handler s n f b input mapValue value result actual p output tlsValue counter thread panicked w).answer = .returned (.ok arc))
    (payload : Data)
    (returned : (reply handler s n f b input mapValue value result actual p output tlsValue counter thread panicked arc w).answer = .returned (.ok payload))
    (takenPayload : Data)
    (taken :
      let c := PV_THR2_ScopeOriginalCaptures.atCaptures s n f b input mapValue value result actual p output tlsValue counter thread panicked arc
      let capture := PV_THR2_RunClosureCapture.scopeValue (PV_THR2_WrapRunEntryCaptures.atCaptures s n f b input mapValue value result actual p output tlsValue).frame.activation
      let d := (PV_THR2_Catch316Entry.segment c capture payload).callback
      let place := PV_THR2_Catch219IntrinsicCapture.sourcePlace c capture
      (PV_THR2_Catch316Reply410.reply (PV_THR2_FnOnceDispatch.handler handler)
        (PV_THR2_Catch316TakenInvoke.beforeTake d.store d.frame.activation place) place
        (reply handler s n f b input mapValue value result actual p output tlsValue counter thread panicked arc w).world).answer = .returned (.ok takenPayload))
    (kind220 scopeValue kind208 closure : Data) (scopePlace : Address)
    (shape220 : takenPayload = PV_THR2_KeyValues.pack kind220 [scopeValue])
    (shape208 : scopeValue = PV_THR2_KeyValues.pack kind208
      [closure,PV_STX2_TypedReferences.reference scopePlace .null]) :
    let programs := PV_THR2_Source15Table.resolve (PV_THR2_OwnInitChildren.resolve (PV_THR2_SourceSpawnTable.resolve (PV_THR2_Source270Table.resolve (PV_THR2_Source361Children.resolve (PV_THR2_Source361HookChildren.resolve (PV_THR2_Source361PacketChildren.resolve (PV_THR2_Source361ScopeChildren.resolve (PV_THR2_Source361BoxTable.resolve (PV_THR2_BoxFromTable.resolve (PV_THR2_Source361InitChildren.resolve fallback))))))))))
    let c := PV_THR2_ScopeOriginalCaptures.atCaptures s n f b input mapValue value result actual p output tlsValue counter thread panicked arc
    let capture := PV_THR2_RunClosureCapture.scopeValue (PV_THR2_WrapRunEntryCaptures.atCaptures s n f b input mapValue value result actual p output tlsValue).frame.activation
    let d := (PV_THR2_Catch316Entry.segment c capture payload).callback
    let place := PV_THR2_Catch219IntrinsicCapture.sourcePlace c capture
    let before := PV_THR2_Catch316TakenInvoke.beforeTake d.store d.frame.activation place
    let r := PV_THR2_Catch316Reply410.reply (PV_THR2_FnOnceDispatch.handler handler) before place (reply handler s n f b input mapValue value result actual p output tlsValue counter thread panicked arc w).world
    let afterTake := PV_THR2_Catch316Returned410.afterStore before d.frame.activation place takenPayload
    let t := PV_THR2_Source15Start.after (PV_THR2_Source220To208.entered
      (PV_THR2_Source316Enter.entered
        (PV_THR2_Catch316PrepareInvoke.afterStore afterTake d.frame.activation takenPayload)
        d.frame.activation d.callers takenPayload) kind220 scopeValue) kind208 closure scopePlace
    let B := PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier (PV_THR2_RangeLiterals.carrier base))) b
    let K := PV_THR2_Scalars.control (PV_THR2_ThreadFields.control ctl)
    let H := PV_THR2_FnOnceDispatch.handler handler
    let fuel := ((((((((PV_THR2_RunEntryMatch.steps n + 2 + 5 + 9 + 1 + 11 + 16 + 4 + 1 + 6 + 8 + 2 + 7 + 14 + 2 + 16 + 1 + 1 + 3 + 3 + 1 + 4 + 1 + 15 + 4 + 2 + 5 + 6 + 1 + 11) + (1+(((5+2)+1)+(1+(8+1)))))) + (1+((5+1)+(1+(8+(3+1))))))+1)+4)+2) + PV_THR2_Source15HandlesToCaptures.steps base b (PV_THR2_Scalars.control (PV_THR2_ThreadFields.control ctl)) (PV_THR2_FnOnceDispatch.handler handler) t.store t.frame.activation t.callers r.world)
    let frontier0 := PV_THR2_Source15AfterHandlesCaptures.after base (PV_THR2_Scalars.control (PV_THR2_ThreadFields.control ctl)) b (PV_THR2_FnOnceDispatch.handler handler) (PV_THR2_Source15Start.after (PV_THR2_Source220To208.entered
              (PV_THR2_Source316Enter.entered
                (PV_THR2_Catch316PrepareInvoke.afterStore afterTake d.frame.activation takenPayload)
                d.frame.activation d.callers takenPayload) kind220 scopeValue) kind208 closure scopePlace).store (PV_THR2_Source15Start.after (PV_THR2_Source220To208.entered
              (PV_THR2_Source316Enter.entered
                (PV_THR2_Catch316PrepareInvoke.afterStore afterTake d.frame.activation takenPayload)
                d.frame.activation d.callers takenPayload) kind220 scopeValue) kind208 closure scopePlace).frame.activation (PV_THR2_Source15Start.after (PV_THR2_Source220To208.entered
              (PV_THR2_Source316Enter.entered
                (PV_THR2_Catch316PrepareInvoke.afterStore afterTake d.frame.activation takenPayload)
                d.frame.activation d.callers takenPayload) kind220 scopeValue) kind208 closure scopePlace).callers r.world ((((((PV_THR2_WrapRunEntryMatch.events (PV_THR2_FnOnceDispatch.handler handler)
          s n f b input mapValue value w ++
        (PV_THR2_WrapRunEntryCallbackReturned.reply handler s n f b input mapValue value result actual p w).events ++
        (PV_THR2_WrapRunEntryActiveChild.reply handler s n f b input mapValue value result actual p output w).events ++ (PV_THR2_ScopeReply121.reply (PV_THR2_FnOnceDispatch.handler handler)
          (PV_THR2_WrapRunEntryScopePrefix.atPrologue s n f b input mapValue value result actual p output tlsValue).store
          (PV_THR2_WrapRunEntryActiveChild.reply handler s n f b input mapValue value result actual p output w).world).events) ++ (PV_THR2_ScopeOriginalReturned122.reply handler s n f b input mapValue value result actual p output tlsValue counter w).events) ++ (PV_THR2_ScopeOriginalReturned123.reply handler s n f b input mapValue value result actual p output tlsValue counter thread w).events) ++ (PV_THR2_ScopeOriginalArcReturned.reply handler s n f b input mapValue value result actual p output tlsValue counter thread panicked w).events) ++ (reply handler s n f b input mapValue value result actual p output tlsValue counter thread panicked arc w).events) ++ r.events) ([PV_THR2_Catch219ToIntrinsic.pending c capture payload])
    let q1 := PV_THR2_OwnUniformSpawnRun.after B K fallback H frontier0
    let P := PV_THR2_Source208Table.table programs
    let q2 := PV_THR2_JoinedCertRegionMetadataPrefix.after B K fallback H q1
    PV_THR2_JoinedCertDispatchTrace.Certificate B K P H (fuel + PV_THR2_OwnUniformSpawnRun.steps B K fallback H frontier0 + PV_THR2_JoinedCertRegionMetadataPrefix.steps B K fallback H q1) ⟨⟨.running (enter PV_THR2_F0.live [.number n,f] s),w,[]⟩,[]⟩ ∧
    PV_THR2_OwnUniformBeforeCertificate.Certificate B K P H (fuel + PV_THR2_OwnUniformSpawnRun.steps B K fallback H frontier0 + PV_THR2_JoinedCertRegionMetadataPrefix.steps B K fallback H q1) ⟨⟨.running (enter PV_THR2_F0.live [.number n,f] s),w,[]⟩,[]⟩ ∧
    PV_THR2_IntrinsicState.advance B K P H (fuel + PV_THR2_OwnUniformSpawnRun.steps B K fallback H frontier0 + PV_THR2_JoinedCertRegionMetadataPrefix.steps B K fallback H q1) ⟨⟨.running (enter PV_THR2_F0.live [.number n,f] s),w,[]⟩,[]⟩ = q2 := by
  intro programs c capture d place before r afterTake t B K H fuel frontier0 q1 P q2
  let initial : PV_THR2_IntrinsicState.State OWNER E := ⟨⟨.running (enter PV_THR2_F0.live [.number n,f] s),w,[]⟩,[]⟩
  have original := PV_THR2_OwnUniformOriginalCaptures.run base ctl fallback handler s n f b input mapValue value result w key mapped error branch variant actual p output field address callback inactive tlsValue tls counter counterReturned thread threadReturned panicked panickedReturned arc arcReturned payload returned takenPayload taken kind220 scopeValue kind208 closure scopePlace shape220 shape208
  have packet := PV_THR2_JoinedCertRegionOriginalCaptures.run base ctl fallback handler s n f b input mapValue value result w key mapped error branch variant actual p output field address callback inactive tlsValue tls counter counterReturned thread threadReturned panicked panickedReturned arc arcReturned payload returned takenPayload taken kind220 scopeValue kind208 closure scopePlace shape220 shape208
  dsimp only at original packet
  have reached : PV_THR2_IntrinsicState.advance B K P H fuel initial = frontier0 := original.2
  have spawnOwner := PV_THR2_OwnUniformSpawnComposition.run B K fallback H frontier0
  have spawned : PV_THR2_IntrinsicState.advance B K P H
      (PV_THR2_OwnUniformSpawnRun.steps B K fallback H frontier0) frontier0 = q1 :=
    (PV_THR2_OwnUniformBeforeCertificate.trace B K P H spawnOwner).symm.trans
      (PV_THR2_OwnUniformSpawnRun.run B K fallback H frontier0)
  have packetTail := PV_THR2_JoinedCertDispatchTrace.append B K P H _ _ _ _ spawned
    (PV_THR2_JoinedCertRegionSpawnComposition.run B K fallback H frontier0)
    (PV_THR2_JoinedCertRegionMetadataPrefix.packet B K fallback H q1)
  have packetAll := PV_THR2_JoinedCertDispatchTrace.append B K P H _ _ _ _ reached packet.1 packetTail
  have ownerTail := PV_THR2_OwnUniformBeforeCertificate.append B K P H _ _ _ _ spawned
    spawnOwner (PV_THR2_JoinedCertRegionMetadataPrefix.owner B K fallback H q1)
  have ownerAll := PV_THR2_OwnUniformBeforeCertificate.append B K P H _ _ _ _ reached original.1 ownerTail
  refine ⟨?_,?_,?_⟩
  · simpa only [Nat.add_assoc] using packetAll
  · simpa only [Nat.add_assoc] using ownerAll
  · rw [PV_THR2_IntrinsicComposition.advance_add,PV_THR2_IntrinsicComposition.advance_add,reached,spawned]
    exact PV_THR2_JoinedCertRegionMetadataPrefix.source B K fallback H q1
#print axioms run
end PV_THR2_JoinedCertRegionOriginalBefore12801
