import S2W_DigestExtraction
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFx_CanonicalExtraction
open Aeneas Aeneas.Std Result

def install (ops : AdapterRw.Ops)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest) : AdapterRw.Ops :=
  {ops with op43 := S2W_DigestExtraction.digest hashv}

def first (ops : AdapterRw.Ops)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest) : S2W_ExtractionBoundary.First :=
  AdapterRw.r1_pool_adapter.owned.stage1_owned (install ops hashv)

def second (ops : AdapterRw.Ops)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest) : S2W_ExtractionBoundary.Second :=
  AdapterRw.r1_pool_adapter.owned.stage2_owned (install ops hashv)

/-- Extraction is constructively inhabited when both natives are the actual
extracted source functions on the same dictionary. No acceptance is asserted. -/
theorem canonical (ops : AdapterRw.Ops)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest) :
    S2W_DigestExtraction.AeneasExtraction (install ops hashv)
      (first ops hashv) (second ops hashv) hashv :=
  ⟨by intros; rfl,by intros; rfl,by intros; rfl⟩

#print axioms canonical
end AspisR1.JFx_CanonicalExtraction
end
