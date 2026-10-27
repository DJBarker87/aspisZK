import GExq_OuterGoodFirst
import GExq_OuterGoodMap
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExq_OuterGoodBinds
open Aeneas Aeneas.Std Result S2W_Trace S2W_Outer GExq_OuterLower GExq_OuterGoodLaws

theorem first_bind {A : Type} (sdk : AdapterRw.Ops)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (law : S2Z.Oracle.NativeBinding sdk hashv)
    (semantic : AdapterRw.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize)
    (k : core.result.Result (alloc.vec.Vec U8) AdapterRw.solana_program_error.ProgramError → Code A)
    (hk : ∀ r, Good hashv (k r)) :
    Good hashv (S2W_Outer.first_decoded sdk traceEffects semantic pub proof split >>= k) :=
  bind_good hashv _ _ (GExq_OuterGoodFirst.first_decoded sdk hashv law semantic pub proof split) hk

theorem map_bind {A B : Type} (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (r : core.result.Result A AdapterRw.aspis_r1_cost_probe.verifier.Error)
    (k : core.result.Result A AdapterRw.solana_program_error.ProgramError → Code B)
    (hk : ∀ r, Good hashv (k r)) :
    Good hashv (mapError traceEffects.op44 r >>= k) :=
  bind_good hashv _ _ (GExq_OuterGoodMap.mapError_good hashv r) hk

#print axioms first_bind
#print axioms map_bind
end AspisR1.GExq_OuterGoodBinds
end
