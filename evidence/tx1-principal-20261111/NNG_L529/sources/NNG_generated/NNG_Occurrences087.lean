import NNG_SilentGraph087
import NNG_Filled087
import NNG_ExpandSemantic087
import NNG_ExpandValues087
import NNG_WideView087
import LIB_Instances
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Occurrences087
open Aeneas Aeneas.Std Result NMP_prepare NMT_CallTree NNG_Observed136

theorem filled (env : RSL.Env) (n : Usize) (bound : n.val≤32768) :
 LIB_Instances.VL.filled.run n.val env
   (observation NNG_Filled087.port (NNG_Events087.events env)
    (invoke "TX1:064/filled" (n,0#u8) (NNG_Filled087.call env core.marker.CopyU8 n 0#u8))) := by
 rw [NNG_SilentGraph087.observation env _ _ _ _ _ (NNG_Filled087.projected env n)
   (NNG_Events087.silent env _ _ _ (by decide) (by decide))]
 exact ⟨bound,rfl⟩

theorem semantic (env : RSL.Env) (src before : Slice U8)
 (srcSize : src.val.length=7015) (dstSize : before.val.length=13831) :
 LIB_Instances.VL.expandSemantic.run (LIB_Carriers.bytes src,LIB_Carriers.bytes before) env
   (observation NNG_ExpandSemantic087.port (NNG_Events087.events env)
    (invoke "TX1:098/expand_semantic" (src,before) (NNG_ExpandSemantic087.call src before))) := by
 rw [NNG_SilentGraph087.observation env _ _ _ _ _ (NNG_ExpandSemantic087.projected src before env)
   (NNG_Events087.silent env _ _ _ (by decide) (by decide))]
 refine ⟨?_,rfl⟩
 change (LIB_Carriers.bytes src).length=7015 ∧ (LIB_Carriers.bytes before).length=13831
 simpa only [NMS_R2N_RSLScalars.bytes_length] using And.intro srcSize dstSize

theorem values (env : RSL.Env) (src before : Slice U8)
 (srcSize : src.val.length=464) (dstSize : before.val.length=928) :
 LIB_Instances.VL.expandValues.run (LIB_Carriers.bytes src,LIB_Carriers.bytes before) env
   (observation NNG_ExpandValues087.port (NNG_Events087.events env)
    (invoke "TX1:099/expand_values" (src,before) (NNG_ExpandValues087.call src before))) := by
 have good : LIBC_ExpandValues.Good (LIB_Carriers.bytes src,LIB_Carriers.bytes before) := by
  change (LIB_Carriers.bytes src).length%16=0 ∧ (LIB_Carriers.bytes before).length=2*(LIB_Carriers.bytes src).length
  simp only [NMS_R2N_RSLScalars.bytes_length,srcSize,dstSize]
  decide
 rw [NNG_SilentGraph087.observation env _ _ _ _ _ (NNG_ExpandValues087.projected src before env good)
   (NNG_Events087.silent env _ _ _ (by decide) (by decide))]
 refine ⟨?_,rfl⟩
 change (LIB_Carriers.bytes src).length≤1856 ∧ (LIB_Carriers.bytes before).length≤3712
 rw [NMS_R2N_RSLScalars.bytes_length,NMS_R2N_RSLScalars.bytes_length,srcSize,dstSize]
 exact ⟨by decide,by decide⟩

theorem view (env : RSL.Env) (proof semantic y1 : Slice U8)
 (domain : LIBC_WideView.Domain (LIB_Carriers.bytes proof,LIB_Carriers.bytes semantic,LIB_Carriers.bytes y1)) :
 LIB_Instances.VL.wideView.run (LIB_Carriers.bytes proof,LIB_Carriers.bytes semantic,LIB_Carriers.bytes y1) env
   (observation NNG_WideView087.port (NNG_Events087.events env)
    (invoke "TX1:095/wide_view" (proof,semantic,y1) (NNG_WideView087.call proof semantic y1))) := by
 rw [NNG_SilentGraph087.observation env _ _ _ _ _ (NNG_WideView087.projected proof semantic y1 env domain)
   (NNG_Events087.silent env _ _ _ (by decide) (by decide))]
 exact ⟨domain,rfl⟩
#print axioms filled
#print axioms semantic
#print axioms values
#print axioms view
end AspisR1.NNG_Occurrences087
