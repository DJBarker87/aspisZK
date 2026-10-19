import AspisR1RhoDiagnostics.Funs

/-! Diagnostic arguments in the source coefficient loop still execute in the
non-prover build. Prove their complete constructors total before erasing logs.
-/
set_option autoImplicit false
namespace AspisR1.CuSavingsRhoDiagnostics
open Aeneas Aeneas.Std Result AspisR1CuRho

theorem remainder_total (x : U32) : ∃ out : U32,x % field.P = .ok out := by
  obtain ⟨out,hrun,_⟩ := WP.spec_imp_exists (UScalar.rem_spec x (y:=field.P) (by
    rw [field.P]
    decide))
  exact ⟨out,hrun⟩

theorem reduce_total (x : U32) : ∃ out : U32,
    field.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call () x = .ok out := by
  obtain ⟨out,hrun⟩ := remainder_total x
  exact ⟨out,by simpa only [field.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call,hrun,bind_tc_ok]⟩

theorem canonical_total (x : field.QM31) : ∃ out : field.QM31,
    field.canonical_qm31 x = .ok out := by
  obtain ⟨a,ha⟩ := reduce_total x.c0.a
  obtain ⟨b,hb⟩ := reduce_total x.c0.b
  obtain ⟨c,hc⟩ := reduce_total x.c1.a
  obtain ⟨d,hd⟩ := reduce_total x.c1.b
  exact ⟨⟨⟨a,b⟩,⟨c,d⟩⟩,by simp only [field.canonical_qm31,ha,hb,hc,hd,bind_tc_ok]⟩

theorem from_qm31_total (x : field.QM31) : ∃ out : field.WideExact,
    field.WideExact.from_qm31 x = .ok out := by
  obtain ⟨out,hrun⟩ := canonical_total x
  exact ⟨⟨out,field.QM31.ZERO⟩,by simp only [field.WideExact.from_qm31,hrun,bind_tc_ok]⟩

theorem from_m31_total (x : U32) : ∃ out : field.WideExact,from_m31 x = .ok out := by
  obtain ⟨word,hw⟩ := remainder_total x
  let q : field.QM31 := ⟨⟨word,field.M31.ZERO⟩,field.CM31.ZERO⟩
  obtain ⟨out,ho⟩ := from_qm31_total q
  refine ⟨out,?_⟩
  simpa only [from_m31,
    field.WideExact.Insts.Aspis_r1_rho_diagnosticsScalarCodeField.from_m31,
    field.QM31.Insts.Aspis_r1_rho_diagnosticsScalarCodeField.from_m31,
    field.CM31.Insts.Aspis_r1_rho_diagnosticsScalarCodeField.from_m31,
    field.M31.Insts.Aspis_r1_rho_diagnosticsScalarCodeField.from_m31,
    field.QM31.from_cm31,field.CM31.from_m31,hw,bind_tc_ok,q] using ho

theorem qm31_trace_erased (tag : U16) (index : Usize) (x : field.QM31) :
    (do let value ← field.WideExact.from_qm31 x;trace.value tag index value) = .ok () := by
  obtain ⟨out,hrun⟩ := from_qm31_total x
  simp only [hrun,bind_tc_ok,trace.value]

theorem m31_trace_erased (tag : U16) (index : Usize) (x : U32) :
    (do let value ← from_m31 x;trace.value tag index value) = .ok () := by
  obtain ⟨out,hrun⟩ := from_m31_total x
  simp only [hrun,bind_tc_ok,trace.value]

#print axioms from_qm31_total
#print axioms from_m31_total
#print axioms qm31_trace_erased
#print axioms m31_trace_erased
end AspisR1.CuSavingsRhoDiagnostics
