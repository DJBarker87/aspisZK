import NNT_TopL
import NNT_Field
import NNT_G1aLaw
import NNN_InstalledChecks
import NNH_Run5bNMF
import NNH_Run5bAcceptance
import NNH_Run5bHeadlineB
import NNH_Run5bSplit
import NNH_Run5bFullSpace
#check RSL.TAS.Impl
#print RSL.TAS.Impl
#print RSL.NNT.NNC_NMFPrimeB
#check AspisR1.NNG_Producer136.producer
#check AspisR1.NNG_Producer137.producer
#check AspisR1.NNG_Producer087.producer
#check AspisR1.NNG_ProducerFull094.producer
#check AspisR1.NNG_Producer328.producer
#check NMX_R3_RegistryRoot.root
#check NMX_R3_RegistryRoot.implementation
#check NMX_R3_DecoderFold.root
#check AspisR1.NNG_ActualCandidate345.candidate
#check AspisR1.NNH_Run5bNMF.nmfB
#check AspisR1.NNH_Run5bNMF.selected
#check AspisR1.NNH_Run5bHost.S_host
example {W Tx : Type} (L : S2Trust.Library W (Nat → S2W_NativeConsolidation.Record))
 (copy : S2W_D189Wrappers.Heap (Nat → S2W_NativeConsolidation.Record) → Nat → S2W_D189Wrappers.Payload → S2W_TrustedStd.Outcome (Nat → S2W_NativeConsolidation.Record))
 (std : S2W_TrustedStd.TrustedStd copy) :
 AspisR1.NNH_G1aEnv.sig (AspisR1.NNH_Run5bHost.S_host (Tx := Tx) L copy std) =
 AspisR1.NNH_Run5bHost.S_host (Tx := Tx) L copy std := rfl
