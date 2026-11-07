import NNH_G1aEnv
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_064World
open Aeneas Aeneas.Std NLW_Full064
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/--064 reads no external caller frame. Rebuild its parser/marker annotations
at the actual frame while preserving the SAME arguments, children, endpoint,
native records and digest trace. This changes no allocator-state output. -/
theorem transport {A B X : Type} (H : Bytes → State) (s : Frame A X)
 (after : NLM_PacketTypes.World B) :
 ∀ outcome events, NMN_064.Native H s outcome events →
 ∃ next, NMN_064.Native H (⟨s.args,after⟩ : Frame B X) outcome next := by
 intro outcome events native
 cases native with
 | observed parsed children parser child =>
   have run := NMN_064.Native.observed (H := H) (s := (⟨s.args,after⟩ : Frame B X))
    parsed children parser child
   refine ⟨(NMN_OracleFold.run H (⟨s.args,after⟩ : Frame B X) parsed children).2,?_⟩
   cases parsed with
   | fail e => exact run
   | div => exact run
   | ok reply => cases reply with
     | Err e => exact run
     | Ok v => exact run
#print axioms transport
end AspisR1.NNH_064World
