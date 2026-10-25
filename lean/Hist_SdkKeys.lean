import Hist_Authority
import SInt2_AcceptedPairClaims
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hist_SdkKeys
open Aeneas Aeneas.Std Result S2W_D189Entry
open ClaimsUnrolledSdk

/-- Installing documented pure key equality commutes with the existing
candidate SDK/S1/Claims installation; no verifier child slot is changed. -/
theorem commute (adapter : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls) :
    sdkOps (Hist_Authority.install adapter) ops B std = Hist_Authority.install (sdkOps adapter ops B std) := rfl

theorem native_owner (adapter : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (sdkOps (Hist_Authority.install adapter) ops B std) native1 native2 hashv)
    (program : S2W_ExtractionBoundary.Program) (e : Entry) (data : Slice U8) (saved : alloc.vec.Vec U8)
    (accepted : native1 program e.first data = ok (.Ok saved)) :
    (e.records (e.handles 2).1).owned.owner = program := by
  rw [extraction.stage1,commute] at accepted
  obtain ⟨account,index,owner⟩ := Hist_Authority.accepted_owner (sdkOps adapter ops B std) program e.first data saved accepted
  have same := Result.ok.inj (index.symm.trans (first_index e).2.2)
  subst account
  exact owner

#print axioms commute
#print axioms native_owner
end AspisR1.Hist_SdkKeys
end
