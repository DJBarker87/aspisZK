import NKL_ChunkCanonical
set_option autoImplicit false
noncomputable section
namespace NKL_ChildCanonical
open Aeneas Aeneas.Std Result AspisR1
open OraclePortCompactDraft MultiproofConeCanonical
open NFU_Retarget
attribute [local instance] Classical.propDecidable

theorem compact (bytes : Slice U8) (aligned:bytes.val.length%16=0) :
 NKL_CanonicalChildren.compactGood bytes=true ↔ canonical (bytesOf bytes.val) := by
 have eq : NKL_CanonicalChildren.compactGood bytes=
  LPl_Kit_Bytes.chunksValid 16 4 false bytes.val := by
  unfold NKL_CanonicalChildren.compactGood LPl_Kit_Bytes.chunksValid
  congr 1
  funext i
  exact LPl.Check.stage bytes.val i
 rw [eq]
 exact NKL_ChunkCanonical.blocks bytes.val 4 (by decide) aligned

theorem echeck (bytes : Slice U8) (aligned:bytes.val.length%32=0) :
 NKL_CanonicalChildren.echeckGood bytes=true ↔ canonical (bytesOf bytes.val) := by
 have eq : NKL_CanonicalChildren.echeckGood bytes=
  LPl_Kit_Bytes.chunksValid 32 8 false bytes.val := by
  unfold NKL_CanonicalChildren.echeckGood LPl_Kit_Bytes.chunksValid
  congr 1
  funext i
  exact LPl.Echeck.chunk_eq _ false
 rw [eq]
 exact NKL_ChunkCanonical.blocks bytes.val 8 (by decide) aligned

theorem compact_decide (bytes : Slice U8) (aligned:bytes.val.length%16=0) :
 NKL_CanonicalChildren.compactGood bytes=decide (canonical (bytesOf bytes.val)) := by
 have meaning:=compact bytes aligned
 cases h:NKL_CanonicalChildren.compactGood bytes <;> simp_all

theorem echeck_decide (bytes : Slice U8) (aligned:bytes.val.length%32=0) :
 NKL_CanonicalChildren.echeckGood bytes=decide (canonical (bytesOf bytes.val)) := by
 have meaning:=echeck bytes aligned
 cases h:NKL_CanonicalChildren.echeckGood bytes <;> simp_all

#print axioms compact
#print axioms echeck
#print axioms compact_decide
#print axioms echeck_decide
end NKL_ChildCanonical
end
