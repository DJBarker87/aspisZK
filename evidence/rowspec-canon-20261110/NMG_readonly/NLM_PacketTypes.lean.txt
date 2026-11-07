import NLF_SdkBorrowLaw
import NJU_Log
set_option autoImplicit false
namespace NLM_PacketTypes
/-- Account/cell/token state and the entire unrelated caller frame. Internal
allocations are represented in returned owned values and the invocation trace;
Ambient is caller-owned memory outside the callee footprint, not allocator state. -/
structure World (Ambient : Type) where
 sdk : NLF_SdkModel.State
 returnData : List UInt8
 ambient : Ambient
/-- Full result and attempted chronological trace, including the first
fail/div, plus the external post-frame at that same invocation. -/
structure Observation (Ambient Event Reply : Type) where
 post : World Ambient
 run : NJU_Log.Run Event Reply
end NLM_PacketTypes
