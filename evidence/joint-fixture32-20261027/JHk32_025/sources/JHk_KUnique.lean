import SAQ_Inverse
import CheckpointBytes5Output
set_option autoImplicit false
namespace AspisR1.JHk_KUnique
open Aeneas Aeneas.Std AspisR1Stage2
theorem source (x y : aspis_core.field.QM31)
    (hx : Port3_FlushInstall.Canonical x) (hy : Port3_FlushInstall.Canonical y)
    (same : CheckpointBytes5Output.ofK x=CheckpointBytes5Output.ofK y) : x=y := by
  rcases x with ⟨⟨a,b⟩,⟨c,d⟩⟩
  rcases y with ⟨⟨a1,b1⟩,⟨c1,d1⟩⟩
  congr 2
  · exact SAQ_Inverse.canonical_injective _ _ hx.1 hy.1 (congrArg (fun z => z.re.re) same)
  · exact SAQ_Inverse.canonical_injective _ _ hx.2.1 hy.2.1 (congrArg (fun z => z.re.im) same)
  · exact SAQ_Inverse.canonical_injective _ _ hx.2.2.1 hy.2.2.1 (congrArg (fun z => z.im.re) same)
  · exact SAQ_Inverse.canonical_injective _ _ hx.2.2.2 hy.2.2.2 (congrArg (fun z => z.im.im) same)
#print axioms source
end AspisR1.JHk_KUnique
