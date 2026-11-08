import NNG_TotalParse094
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_ParseOriginal094
open Aeneas Aeneas.Std Result RSL
/-- The total source parser reads the original logical bytes through its
native carrier even off the representable-length domain. No byte-identity
assumption is made for a stopped/rejected original input. -/
theorem model (proof : Bytes) (env : Env) :
 LIBC_ParseShape.model (LIB_Carriers.bytes (LIBC_Bytes.raw proof)) env =
 LIBC_ParseShape.model proof env := by
 unfold LIBC_ParseShape.model
 rw [LIBC_Bytes.from_native]
#print axioms model

theorem occurrence (proof : Bytes) (env : Env) :
 LIB_Instances.VL.parseShape.run proof env
  (LIB_Carriers.resultObs NNG_ParseCall094.port [] (NNG_ParseCall094.call env (LIBC_Bytes.raw proof))) := by
 refine ⟨True.intro,?_⟩
 apply (LIB_ParseShapeTotal.graph proof env _).mpr
 have same := NNG_ParseCall094.graph env (LIBC_Bytes.raw proof)
 apply (LIBC_ParseShape.graph _ env _).mp at same
 rw [model] at same
 exact same
#print axioms occurrence
end AspisR1.NNG_ParseOriginal094
