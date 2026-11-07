import LIB_Carriers
import LIB_Mark
import NMS_R2GetterLink
set_option autoImplicit false
noncomputable section
namespace LIB_Transcribed
open Aeneas Aeneas.Std AdapterRw
/-- Full getter law, including nonempty BorshIoError clone allocation. -/
theorem data (a : r1_pool_adapter.owned.OwnedAccount) :
    NMS_R2N_Interpreted.Simulates (NMS_R2N_RSLError.reply LIB_Carriers.bytes)
      (NMS_R2N_GetterMeaning.meaning a)
      (NMS_R2N_RSLPoolCarriers.account a).data := NMS_R2GetterLink.full a
#print axioms data
end LIB_Transcribed
