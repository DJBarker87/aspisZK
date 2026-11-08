import NNG_Producer345
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Candidate345

/-- The source certificate and full logical row are proved together at fixed
concrete fields. No accuracy field is assumed of an arbitrary producer. -/
structure Certificate : Prop where
 model : RSL.TX1_345.RowSpec_345 LIB_Instances.VL LIB_Instances.P LIB_Instances.C NNG_Producer345.producer
 native : ∀ (W : Type) (s : NMT_345.Parent W) (env : RSL.Env),
  NNG_Native345.producer s env=NNG_Producer345.producer (NNG_ProjectFrames345.original s) env
 reified : ∀ (a : RSL.TX1_345.Args) (h : NNG_Reify345.representable a) (env : RSL.Env),
  NNG_Native345.producer (NNG_Reify345.input a h) env=NNG_Producer345.producer a env

theorem certificate : Certificate :=
 ⟨NNG_Model345.reference,fun _=>NNG_Producer345.native,NNG_Producer345.reified⟩

/-- Complete concrete revision4 candidate: original Domain True, no child,
library, successful-return or representability hypothesis in the row. -/
theorem candidate : RSL.TX1_345.RowSpec_345 LIB_Instances.VL LIB_Instances.P LIB_Instances.C
 NNG_Producer345.producer := certificate.model
#print axioms certificate
#print axioms candidate
end AspisR1.NNG_Candidate345
