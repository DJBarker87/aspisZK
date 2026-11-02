import R1Z.PV_RunJoin_PolyPayloadCanonicalWindow73
import R1Z.PV_RunJoin_NativePolynomialBytes72
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativePolynomialByteDomain73
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63
abbrev Q := aspis_core.field.QM31

theorem complete {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F) (values : Array Q 28#usize) :
    ∃ bytes,@host_sumcheck.encode_polynomial (types base) (opsNative base heap box ops runtime world) values=ok bytes ∧
      bytes.val.length=896 ∧ ∀ i : Nat,i<28 →
      ∃ w : aspis_core.field.wide_exact.WideExact,
        (bytes.val.drop (32*i)).take 32=(PV_RunJoin_FlatBytes35.wire w).val ∧
        PV_RunJoin_WideLimbsParse72.Canonical w ∧
        w.c1=⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩ := by
  obtain ⟨bytes,hb,hv,hl⟩ := PV_RunJoin_NativePolynomialBytes72.complete base heap box ops runtime world values
  refine ⟨bytes,hb,hl,?_⟩
  intro i hi
  rw [hv]
  exact PV_RunJoin_PolyPayloadCanonicalWindow73.complete (PV_RunJoin_InterpolationInput72.cells values) 0 28 i hi

#print axioms complete
end R1Z.PV_RunJoin_NativePolynomialByteDomain73
