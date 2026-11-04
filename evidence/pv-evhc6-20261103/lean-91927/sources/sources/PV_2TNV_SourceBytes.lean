import PV_2TNV_CanonicalWitness
import JFx_NativeBytes
import JHb_DataRequest
set_option autoImplicit false
noncomputable section
namespace AspisR1.PV_2TNV_SourceBytes
open Aeneas Aeneas.Std R1Z PV_2TNV_PublicEncoding
local instance : CharP K 2147483647 :=
  charP_of_injective_algebraMap (algebraMap (ZMod AspisCircleGroupOrder.P) K).injective
    AspisCircleGroupOrder.P

theorem public_alias : JFx_NativeBytes.publicInput.val = JFx_DataPublic00.bytes := rfl

theorem request_alias : JHb_DataRequest.value.val = JHb_DataRequest.bytes := rfl

theorem transfer_tag : JFx_NativeBytes.publicInput.val[6]? = some (1#u8) := rfl

theorem native_payment_bytes : JHb_DataRequest.value.val.drop 104 =
    JFx_NativeBytes.publicInput.val.drop 1664 := PV_2TNV_ByteEncoding.payment_same

theorem native_payment_projection : payment (JHb_DataRequest.value.val.drop 104) =
    payment (JFx_NativeBytes.publicInput.val.drop 1664) := payment_association

/-- A mathematical fibre for the explicit byte-derived public; no wrapper or
runtime association is asserted by this helper. -/
theorem byte_derived_fibre {CommitHandle : Type} (handle : CommitHandle) :
    JFx_NativeBytes.publicInput.val = JFx_DataPublic00.bytes ∧
    (∃ w : (BuilderSource.prover (K := K)).Instance,
      (BuilderSource.prover (K := K)).public w = (x handle).1) :=
  ⟨public_alias,PV_2TNV_CanonicalWitness.fibre handle⟩

#print axioms public_alias
#print axioms request_alias
#print axioms transfer_tag
#print axioms native_payment_bytes
#print axioms native_payment_projection
#print axioms byte_derived_fibre
end AspisR1.PV_2TNV_SourceBytes
