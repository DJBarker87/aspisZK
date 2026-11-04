import NBG_WideCarriers
import NBG_Transport
set_option autoImplicit false
noncomputable section
namespace NFD_RawCarriers
open Aeneas Aeneas.Std
abbrev Wide := FIo_Native.aspis_core.field.wide_exact.WideExact

def make (a b c d e f g h : U32) : Wide :=
  ⟨⟨⟨a,b⟩,⟨c,d⟩⟩,⟨⟨e,f⟩,⟨g,h⟩⟩⟩
theorem raw_roundtrip (x : Wide) :
    make x.c0.c0.a x.c0.c0.b x.c0.c1.a x.c0.c1.b
      x.c1.c0.a x.c1.c0.b x.c1.c1.a x.c1.c1.b = x := rfl

theorem limbs_result_state_effects {State : Type} (x : Wide) (state : State) :
    (FIo_Native.aspis_core.field.wide_exact.WideExact.to_limbs x,state,([] : List Unit)) =
    (Result.ok (Array.make 8#usize [x.c0.c0.a,x.c0.c0.b,x.c0.c1.a,x.c0.c1.b,
      x.c1.c0.a,x.c1.c0.b,x.c1.c1.a,x.c1.c1.b]),state,[]) := by
  rw [NBG_WideCarriers.to_limbs_result]

def fromPort : NBG_Transport.CV → NBG_Transport.V
  | .S1 => .S1 | .S2 => .S2 | .D => .D
theorem tag_roundtrip (v : NBG_Transport.V) : fromPort (NBG_Transport.port v)=v := by
  cases v <;> rfl

theorem tag_result_state_effects {State : Type} (v : NBG_Transport.V) (state : State) :
    (AspisR1PublicPreparation.transport.Variant.tag v,state,([] : List Unit)) =
    (AspisR1.CheckpointBytes4Ops.tag (NBG_Transport.port v),state,[]) := by
  rw [NBG_Transport.tag_result]

#print axioms raw_roundtrip
#print axioms limbs_result_state_effects
#print axioms tag_roundtrip
#print axioms tag_result_state_effects
end NFD_RawCarriers
