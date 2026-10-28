import JHk_KUnique
import JHl_ClaimKappa
import JFq_Claim
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHm_ClaimCarriers
open Aeneas Aeneas.Std AspisR1CurrentPreparedClaim Concrete

def native (x : AspisR1Stage2.aspis_core.field.wide_exact.WideExact) : E :=
  ⟨⟨⟨x.c0.c0.a,x.c0.c0.b⟩,⟨x.c0.c1.a,x.c0.c1.b⟩⟩,
    ⟨⟨x.c1.c0.a,x.c1.c0.b⟩,⟨x.c1.c1.a,x.c1.c1.b⟩⟩⟩

theorem decodeNative (x : AspisR1Stage2.aspis_core.field.wide_exact.WideExact) :
    decode (native x)=CheckpointBytes5Output.ofE x := rfl
#print axioms decodeNative

theorem unique (x y : E) (hx : Canonical x) (hy : Canonical y) (same : decode x=decode y) : x=y := by
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
#print axioms unique
def gamma : E := ⟨⟨⟨855639275#u32,1483149559#u32⟩,⟨1898717401#u32,1849775942#u32⟩⟩,⟨⟨1112406525#u32,1796814865#u32⟩,⟨1838939499#u32,418714188#u32⟩⟩⟩
theorem gammaCanonical : Canonical gamma := by decide
#print axioms gammaCanonical
theorem gammaNative : native JFq_Gamma.scalar=gamma := rfl
#print axioms gammaNative
def kappa : E := ⟨⟨⟨1116662073#u32,1579954339#u32⟩,⟨1176243488#u32,728698552#u32⟩⟩,⟨⟨640606056#u32,1197281433#u32⟩,⟨2141139535#u32,1224613133#u32⟩⟩⟩
theorem kappaCanonical : Canonical kappa := by decide
#print axioms kappaCanonical
theorem kappaNative : native JFq_Kappa.scalar=kappa := rfl
#print axioms kappaNative
def claim : E := ⟨⟨⟨1653632192#u32,1119241674#u32⟩,⟨1504411203#u32,1216841972#u32⟩⟩,⟨⟨2000740570#u32,1632264801#u32⟩,⟨1558325561#u32,1283233474#u32⟩⟩⟩
theorem claimCanonical : Canonical claim := by decide
#print axioms claimCanonical
theorem claimNative : native JFq_Claim.scalar=claim := rfl
#print axioms claimNative
end AspisR1.JHm_ClaimCarriers
end
