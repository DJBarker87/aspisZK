import NHW_DeployedQuery
import NHW_MaskInjective
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHW_FieldTransport
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody
abbrev Q := aspis_core.field.QM31
abbrev E := aspis_core.field.wide_exact.WideExact
/-- Canonical limb transport between the two retained arithmetic carriers. -/
theorem canonical_current (x : Q) (hx : NBF_PowerStep.Canonical x) :
 AspisR1CurrentWide.Proof.CanonicalQM (SAQ_WideABI.toQ x) :=
 ⟨⟨hx 0,hx 1⟩,⟨hx 2,hx 3⟩⟩
/-- Full Result equality on canonical inputs, including totality. The
three source/probe value laws are reused; multiplication is never sent to Kani. -/
theorem power (x y : Q) (hx : NBF_PowerStep.Canonical x)
 (hy : NBF_PowerStep.Canonical y) :
 SAQ_Arithmetic.mulK x y=NBO_FieldSemantics.power x y := by
 have cx := canonical_current x hx
 have cy := canonical_current y hy
 obtain ⟨probe,probeRun,probeCanonical,probeValue⟩ :=
   ExtractedCurrentQM31Exact.current_qm_mul_exact
     (AspisR1CurrentWide.Proof.toQM (SAQ_WideABI.toQ x))
     (AspisR1CurrentWide.Proof.toQM (SAQ_WideABI.toQ y)) cx cy
 obtain ⟨out,run,last⟩ := Port3_PushFrame.bind_success _ _ _
   ((AspisR1CurrentWide.Proof.qm_mul_same (SAQ_WideABI.toQ x) (SAQ_WideABI.toQ y)).trans probeRun)
 have value := AspisR1CurrentWide.Proof.qm_mul_success _ _ out cx cy run
 obtain ⟨mask,maskRun,maskCanonical,maskValue⟩ :=
   ExtractedMaskQM31Exact.current_qm_mul_exact (NBO_FieldPorts.toQ x) (NBO_FieldPorts.toQ y)
     ((NBO_FieldPorts.canonicalQ x).mp hx) ((NBO_FieldPorts.canonicalQ y).mp hy)
 have outCanonical : ExtractedMaskQM31Exact.CurrentCanonicalQM (NBO_FieldPorts.toQ (SAQ_WideABI.fromQ out)) := by
   rcases value.1 with ⟨⟨a,b⟩,c,d⟩
   exact ⟨⟨a,b⟩,c,d⟩
 have same : NBO_FieldPorts.toQ (SAQ_WideABI.fromQ out)=mask :=
   (NHW_MaskInjective.decode_eq_iff _ _ outCanonical maskCanonical).mp
     (value.2.trans maskValue.symm)
 have back := congrArg NBO_FieldPorts.fromQ same
 simp only [NBO_FieldPorts.q_roundtrip] at back
 simp only [SAQ_Arithmetic.mulK,NBO_FieldSemantics.power,run,maskRun,bind_tc_ok,back]
theorem add_q (x y : Q) (hx : NBF_PowerStep.Canonical x)
 (hy : NBF_PowerStep.Canonical y) :
 (do let z ← AspisR1CurrentWide.field.QM31.add (SAQ_WideABI.toQ x) (SAQ_WideABI.toQ y);ok (SAQ_WideABI.fromQ z))=
 (do let z ← AspisR1SelectedMaskProbe.field.QM31.add (NBO_FieldPorts.toQ x) (NBO_FieldPorts.toQ y);ok (NBO_FieldPorts.fromQ z)) := by
 have cx := canonical_current x hx
 have cy := canonical_current y hy
 obtain ⟨probe,probeRun,probeCanonical,probeValue⟩ :=
   ExtractedCurrentQM31Exact.current_qm_add_exact
     (AspisR1CurrentWide.Proof.toQM (SAQ_WideABI.toQ x))
     (AspisR1CurrentWide.Proof.toQM (SAQ_WideABI.toQ y)) cx cy
 obtain ⟨out,run,last⟩ := Port3_PushFrame.bind_success _ _ _
   ((AspisR1CurrentWide.Proof.qm_add_same (SAQ_WideABI.toQ x) (SAQ_WideABI.toQ y)).trans probeRun)
 have value := AspisR1CurrentWide.Proof.qm_add_success _ _ out cx cy run
 obtain ⟨mask,maskRun,maskCanonical,maskValue⟩ :=
   ExtractedMaskQM31Exact.current_qm_add_exact (NBO_FieldPorts.toQ x) (NBO_FieldPorts.toQ y)
     ((NBO_FieldPorts.canonicalQ x).mp hx) ((NBO_FieldPorts.canonicalQ y).mp hy)
 have outCanonical : ExtractedMaskQM31Exact.CurrentCanonicalQM (NBO_FieldPorts.toQ (SAQ_WideABI.fromQ out)) := by
   rcases value.1 with ⟨⟨a,b⟩,c,d⟩
   exact ⟨⟨a,b⟩,c,d⟩
 have same : NBO_FieldPorts.toQ (SAQ_WideABI.fromQ out)=mask :=
   (NHW_MaskInjective.decode_eq_iff _ _ outCanonical maskCanonical).mp
     (value.2.trans maskValue.symm)
 have back := congrArg NBO_FieldPorts.fromQ same
 simp only [NBO_FieldPorts.q_roundtrip] at back
 simp only [run,maskRun,bind_tc_ok,back]

theorem add (x y : E) (hx : NBO_TailDomain.WideCanonical x)
 (hy : NBO_TailDomain.WideCanonical y) :
 SAQ_Arithmetic.add x y=NBO_FieldSemantics.add x y := by
 have h0 := add_q x.c0 y.c0 hx.1 hy.1
 have h1 := add_q x.c1 y.c1 hx.2 hy.2
 have shell : SAQ_Arithmetic.add x y = (do
   let a ← (do let z ← AspisR1CurrentWide.field.QM31.add (SAQ_WideABI.toQ x.c0) (SAQ_WideABI.toQ y.c0);ok (SAQ_WideABI.fromQ z))
   let b ← (do let z ← AspisR1CurrentWide.field.QM31.add (SAQ_WideABI.toQ x.c1) (SAQ_WideABI.toQ y.c1);ok (SAQ_WideABI.fromQ z))
   ok (⟨a,b⟩ : E)) := by
   simp only [SAQ_Arithmetic.add,AspisR1CurrentWide.field.wide_exact.WideExact.add,
     SAQ_WideABI.toW,SAQ_WideABI.fromW,bind_assoc_eq,bind_tc_ok]
 rw [shell,h0,h1]
 simp only [NBO_FieldSemantics.add,NBO_FieldPorts.fromE,bind_assoc_eq,bind_tc_ok]
#print axioms add
#print axioms add_q
#print axioms canonical_current
#print axioms power
end AspisR1.NHW_FieldTransport
