import RPv_FJh_Native07RawValue
import RPv_FJh_WidePack
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJh_Native07RawWide
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)
open FIw_ArrayValue (canonical decoded)
open FJa_PoseidonOrigins (Openings Selectors)
open FIz_ConcretePack (embed)
def pack (v : Fin 16 → K) (g : Fin 4) := R0P.pack4 ConcretePackBasis.basis
  (fun j=>embed (v (FJe_ExternalAdjoint.lane g j)))
def model (o : Openings) (s : Selectors) (g : Fin 4) := embed (decode s.block) *
  (embed (decoded s.local ⟨(0#usize).val,by decide⟩) *
    (pack (decoded o.succ_z) g-pack (R0P.poseidonLeadingPair (decoded o.z) (decoded o.xor12_z)) g)+
  embed (decoded s.local ⟨1,by decide⟩+decoded s.local ⟨9,by decide⟩+decoded s.local ⟨10,by decide⟩)*
    (pack (decoded o.succ_z) g-pack (R0P.poseidonInterpolatedFullPair (decoded o.z) (decoded s.local)) g)+
  embed ((List.ofFn (fun i : Fin 7=>decoded s.local ⟨i.val+2,by change i.val+2<16;omega⟩)).foldl (·+·) 0)*
    (pack (decoded o.succ_z) g-pack (R0P.poseidonInterpolatedInternalPair (decoded o.z) (decoded s.local)) g))
/-- Explicit Wide transport of the complete native arithmetic value on the
same input cells. A Wide scalar-family interpretation is still separate. -/
theorem value (o : Openings) (s : Selectors) (out : Array NQ 4#usize)
    (hz : canonical o.z) (ht : canonical o.succ_z) (hx : canonical o.xor12_z)
    (hs : canonical s.local) (hb : Canon s.block)
    (run : state_only_poseidon.evaluate_state_only_poseidon_oracle_projected o s=ok out) :
    canonical out ∧ (fun g=>embed (decoded out g))=model o s := by
  have v := FJh_Native07RawValue.value o s out hz ht hx hs hb run
  refine ⟨v.1,?_⟩
  funext g
  refine (congrArg embed (congrFun v.2 g)).trans ?_
  unfold FJh_Native07RawValue.model model pack
  simp only [map_mul,map_add,map_sub,FJh_WidePack.value]
#print axioms value
end AspisR1.FJh_Native07RawWide
end
