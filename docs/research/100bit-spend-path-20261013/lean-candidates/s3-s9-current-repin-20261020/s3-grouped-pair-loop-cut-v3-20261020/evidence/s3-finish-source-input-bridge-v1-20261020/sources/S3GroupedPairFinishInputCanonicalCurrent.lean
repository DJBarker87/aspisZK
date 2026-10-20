import CurrentFinishField
import S3GroupedPairRealAddCurrent

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1GroupedPairCut.Proofs.FinishInputCanonicalCurrent

abbrev S := AspisR1GroupedPairCut.field.WideExact
abbrev FinishE := AspisR1CurrentWide.Proof.FinishE

def finishToS (x : FinishE) : S :=
  AspisR1GroupedPairCut.Proofs.RealAddCurrent.fromE (AspisR1CurrentWide.Proof.ofFinishE x)

theorem finish_canonical_to_s3 (x : FinishE)
    (hx : AspisR1CurrentWide.Proof.CanonicalFinish x) :
    AspisR1GroupedPairCut.Proofs.RealAddCurrent.Canonical (finishToS x) := by
  change AspisR1CurrentWide.Proof.CanonicalWide
    (AspisR1GroupedPairCut.Proofs.RealAddCurrent.toE (finishToS x))
  unfold finishToS
  rw [AspisR1GroupedPairCut.Proofs.RealAddCurrent.to_from]
  exact hx

theorem finishField_s3_canonical (bytes : Slice U8) (i : Usize) (x : FinishE)
    (h : AspisR1CurrentWide.Proof.finishField bytes i = .ok x) :
    AspisR1GroupedPairCut.Proofs.RealAddCurrent.Canonical (finishToS x) :=
  finish_canonical_to_s3 x
    (AspisR1CurrentWide.Proof.finishField_success_canonical bytes i x h)

end AspisR1GroupedPairCut.Proofs.FinishInputCanonicalCurrent

#print axioms AspisR1GroupedPairCut.Proofs.FinishInputCanonicalCurrent.finishField_s3_canonical
