import LIB_Carriers
set_option autoImplicit false
namespace LIB_Root0
abbrev root0 := NNC_ByteCarriers.Root0
theorem exact (checkpoint proof : Aeneas.Std.Slice Aeneas.Std.U8) :
    root0 (LIB_Carriers.bytes checkpoint) (LIB_Carriers.bytes proof) ↔
      NLP_InputDomain.Root0 checkpoint proof := NNC_ByteCarriers.root0_native _ _
#print axioms exact
end LIB_Root0
