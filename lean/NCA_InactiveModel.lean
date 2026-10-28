import NBR_OpeningConstruct
import LPi_EWriter
set_option autoImplicit false
namespace AspisR1.NCA_InactiveModel
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisR1CurrentCaller.OriginalSerializerInstallation

/-- The reached inactive value is quantified directly; no serializer success,
canonicality restriction, independent bytes or selected opening is supplied. -/
theorem source (view : verifier.View) :
    NBA_Installed.actual.sampling.toBytes view.inactive = ok (expectedBytes view.inactive) := by
  rw [NBA_Installed.serializer_slot]
  exact sourceBytes_total view.inactive

/-- Exact serializer word order on the same eight-coordinate carrier. -/
theorem words (x : aspis_core.field.WideExact) :
    (expectedBytes x).val =
      [x.c0.c0.a,x.c0.c0.b,x.c0.c1.a,x.c0.c1.b,
       x.c1.c0.a,x.c1.c0.b,x.c1.c1.a,x.c1.c1.b].flatMap
        (fun w => (core.num.U32.to_le_bytes w).val) := by
  obtain ⟨out,call,layout⟩ := LPi_EWriter.source (sourceCarrier x)
  have same : out = expectedBytes x :=
    Result.ok.inj (call.symm.trans (sourceBytes_total x))
  rw [←same]
  exact layout

#print axioms source
#print axioms words
end AspisR1.NCA_InactiveModel
