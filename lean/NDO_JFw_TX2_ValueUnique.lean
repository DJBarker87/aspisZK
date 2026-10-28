import NDO_JFw_TX2_DotsExplicit
import SAQ_Inverse
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_ValueUnique
open Aeneas Aeneas.Std Result

theorem native (x y : FIo_Install.NE) (hx : FIo_WideValues.Canon x)
    (hy : FIo_WideValues.Canon y)
    (same : AspisR1CurrentWide.Proof.decodeWide (FIo_FieldBridge.wide x)=
      AspisR1CurrentWide.Proof.decodeWide (FIo_FieldBridge.wide y)) : x=y := by
  rcases x with ⟨⟨⟨a,b⟩,⟨c,d⟩⟩,⟨⟨e,f⟩,⟨g,h⟩⟩⟩
  rcases y with ⟨⟨⟨a1,b1⟩,⟨c1,d1⟩⟩,⟨⟨e1,f1⟩,⟨g1,h1⟩⟩⟩
  congr 3
  · exact SAQ_Inverse.canonical_injective _ _ hx.1.1.1 hy.1.1.1 (congrArg (fun z => z.re.re.re) same)
  · exact SAQ_Inverse.canonical_injective _ _ hx.1.1.2 hy.1.1.2 (congrArg (fun z => z.re.re.im) same)
  · exact SAQ_Inverse.canonical_injective _ _ hx.1.2.1 hy.1.2.1 (congrArg (fun z => z.re.im.re) same)
  · exact SAQ_Inverse.canonical_injective _ _ hx.1.2.2 hy.1.2.2 (congrArg (fun z => z.re.im.im) same)
  · exact SAQ_Inverse.canonical_injective _ _ hx.2.1.1 hy.2.1.1 (congrArg (fun z => z.im.re.re) same)
  · exact SAQ_Inverse.canonical_injective _ _ hx.2.1.2 hy.2.1.2 (congrArg (fun z => z.im.re.im) same)
  · exact SAQ_Inverse.canonical_injective _ _ hx.2.2.1 hy.2.2.1 (congrArg (fun z => z.im.im.re) same)
  · exact SAQ_Inverse.canonical_injective _ _ hx.2.2.2 hy.2.2.2 (congrArg (fun z => z.im.im.im) same)

#print axioms native
end AspisR1.JFw_TX2_ValueUnique
end
