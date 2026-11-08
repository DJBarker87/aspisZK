import NNH_Run6Fields
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_Run6Installed
open RSL TAS NNH_Libraries
/-- Every implementation slot is literal delivered data; no arbitrary Impl binder. -/
def implementation (allocation217 : Bytes → Env → Bool)
 (allocation234 : TX2_234.Args → Env → Nat → Bool)
 (ch : NMX_R4_Authentication.Choices) (alloc1 alloc2 : NMV_ConcreteWindows.Allocation) : Impl L V0 VL :=
 {
   f136 := NNG_Producer136.producer
   f137 := NNG_Producer137.producer
   f087 := NNG_Producer087.producer
   f094 := NNG_ProducerFull094.producer
   f328 := NNG_Producer328.producer
   f345 := NNG_TotalProducer345.producer
   f217 := NMX_R3_DecoderFold.decode allocation217
   f234 := NMX_R3_RegistryRoot.authenticate allocation234
   f233 := NMX_R4_Authentication.authenticate ch
   f242 := NMX_R6_Validation.validate ch
   f241 := NMX_R9_StageTwo.stage2 ch
   f064 := NNH_064Install.f064
   f344 := NMV_ConcreteWindows.stage1 alloc1 NNG_TotalProducer345.producer
   f240 := NMV_ConcreteWindows.stage2 alloc2 (NMX_R9_StageTwo.stage2 ch)
   process := NVR_Dispatch.process
    (NMV_ConcreteWindows.stage1 alloc1 NNG_TotalProducer345.producer)
    (NMV_ConcreteWindows.stage2 alloc2 (NMX_R9_StageTwo.stage2 ch))
   entry := NVR_Dispatch.entry (NVR_Dispatch.process
    (NMV_ConcreteWindows.stage1 alloc1 NNG_TotalProducer345.producer)
    (NMV_ConcreteWindows.stage2 alloc2 (NMX_R9_StageTwo.stage2 ch))) }

theorem installed_same (allocation217 : Bytes → Env → Bool)
 (allocation234 : TX2_234.Args → Env → Nat → Bool)
 (ch : NMX_R4_Authentication.Choices) (alloc1 alloc2 : NMV_ConcreteWindows.Allocation) :
 NNH_Run6Fields.install (implementation allocation217 allocation234 ch alloc1 alloc2)
  allocation217 allocation234 ch alloc1 alloc2 = implementation allocation217 allocation234 ch alloc1 alloc2 := rfl
#print axioms implementation
#print axioms installed_same
end AspisR1.NNH_Run6Installed
end
