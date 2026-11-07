import NNH_S1CodecInspect
import NNH_OptionOk
set_option autoImplicit false
noncomputable section
namespace NNH_S1DecodeOk
open Aeneas Aeneas.Std AspisR1 AdapterRw NND_Carrier NNH_Libraries

def carrier (st : AspisS6CurrentCodecInstallation.Statement) : NMT_345.Statement :=
 NMT_345Dec.fromT8 (AspisS6CurrentAdapterCarrier.toPoolV1PairForestTerminalStatementV1 st)

theorem source (publicData : Slice U8) (st : C.Statement)
 (success : C.decodeStatement (LIB_Carriers.bytes publicData)=some st) :
 ∃ native,AspisS6CurrentCodecInstallation.decode publicData=.ok (.Ok native) ∧ carrier native=st := by
 change LIBC_S1.decode (LIB_Carriers.bytes publicData)=some st at success
 unfold LIBC_S1.decode at success
 split at success
 · rw [LIBC_Bytes.from_native] at success
   unfold NMT_345.decodeCall at success
   cases decoded : AspisS6CurrentCodecInstallation.decode publicData with
   | fail e => simp only [decoded,NMT_345.mapOuter] at success; cases success
   | div => simp only [decoded,NMT_345.mapOuter] at success; cases success
   | ok reply => cases reply with
     | Err e => simp only [decoded,NMT_345.mapOuter,NMT_345.mapCore] at success; cases success
     | Ok native =>
      simp only [decoded,NMT_345.mapOuter,NMT_345.mapCore,Option.some.injEq] at success
      exact ⟨native,rfl,success⟩
 · cases success

#print axioms source
end NNH_S1DecodeOk
