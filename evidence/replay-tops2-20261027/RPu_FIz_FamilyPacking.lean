import RPu_FIz_ScalarAssembly
import RPu_FIz_PackLinear
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIz_FamilyPacking
open FIv_NativeValue (K)
theorem value (p : R0P.Public K) (o : R0P.Openings K) (s : R0P.Sel K) (group : Nat) :
    FIz_ContributionList.fromList (R0P.scheduleFamily.residuals p o s) 0 group+
    FIz_ContributionList.fromList (R0P.pathFamily.residuals p o s) 32 group+
    FIz_ContributionList.fromList (R0P.valueFamily.residuals p o s) 49 group+
    FIz_ContributionList.fromList (R0P.digestFamily.residuals p o s) 84 group+
    FIz_ContributionList.fromList (R0P.assetFamily.residuals p o s) 92 group+
    FIz_ContributionList.fromList (R0P.occupancyFamily.residuals p o s) 0 group=
      FIx_PreweightedPack.pack (fun i=>R0P.SemSource.scalarLaneAt p o s (4*group+i.val)) := by
  unfold FIz_ContributionList.fromList
  simp only [←FIz_PackLinear.add]
  apply congrArg FIx_PreweightedPack.pack
  funext i
  exact FIz_ScalarAssembly.value p o s (4*group+i.val)
#print axioms value
end AspisR1.FIz_FamilyPacking
end
