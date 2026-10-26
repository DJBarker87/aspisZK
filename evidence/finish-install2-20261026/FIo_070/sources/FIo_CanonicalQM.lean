import FIo_QMMulValues
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIo_CanonicalQM
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open FIo_FieldBridge (NQ qm cm)

theorem limb (x z : U32)
    (run : FIo_Native.aspis_core.field.wide_exact.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call () x=ok z) :
    z.val<2147483647 ∧ decodeM z=decodeM x := by
  unfold FIo_Native.aspis_core.field.wide_exact.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call at run
  simp only [FIo_Native.aspis_core.field.P] at run
  obtain ⟨out,hout,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  have same : out=z := Result.ok.inj run
  subst out
  have hz : z.val=x.val%2147483647 := by scalar_tac
  constructor
  · rw [hz]; omega
  · change (z.val : ZMod 2147483647)=(x.val : ZMod 2147483647)
    rw [hz]; simp

theorem value (x z : NQ)
    (run : FIo_Native.aspis_core.field.wide_exact.canonical_qm31 x=ok z) :
    FIo_QMValues.Canon z ∧ decodeQM (qm z)=decodeQM (qm x) := by
  unfold FIo_Native.aspis_core.field.wide_exact.canonical_qm31 at run
  obtain ⟨a,ha,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b,hb,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨c,hc,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨d,hd,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  have same : (⟨⟨a,b⟩,⟨c,d⟩⟩ : NQ)=z := Result.ok.inj run
  subst z
  have va := limb x.c0.a a ha
  have vb := limb x.c0.b b hb
  have vc := limb x.c1.a c hc
  have vd := limb x.c1.b d hd
  refine ⟨⟨⟨va.1,vb.1⟩,⟨vc.1,vd.1⟩⟩,?_⟩
  apply QuadraticAlgebra.ext <;> apply QuadraticAlgebra.ext
  · exact va.2
  · exact vb.2
  · exact vc.2
  · exact vd.2

#print axioms limb
#print axioms value
end AspisR1.FIo_CanonicalQM
end
