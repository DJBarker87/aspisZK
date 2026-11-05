import NGK_COMBINED_IMPORT

set_option autoImplicit false
namespace NIB_FrameValues
open Aeneas Aeneas.Std

theorem set_frame {A E : Type} (state : AspisR1.S2I.ReturnData.State A E)
    (bytes : List U8) :
    (AspisR1.S2I.ReturnData.set state bytes).accounts = state.accounts ∧
    (AspisR1.S2I.ReturnData.set state bytes).returnData = bytes ∧
    (AspisR1.S2I.ReturnData.set state bytes).events = state.events ++ [.setReturnData bytes] :=
  ⟨rfl,rfl,rfl⟩
#print axioms set_frame
end NIB_FrameValues
