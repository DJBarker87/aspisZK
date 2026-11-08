import NNG_ProjectFrames345
import NNG_Windows345
import NNG_ByteGuards345
import NNG_SplitByte345
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_FirstArgs345
open Aeneas Aeneas.Std Result NMT_345

theorem source {W : Type} (s : ProofData W)
 (hd : decodeCall s.publicData=ok (.Ok s.statement))
 (hv : validateCall s.statement=ok (.Ok ()))
 (route : s.data.val.length=2) :
 NNG_ChildSource345.args (semanticValue s.statement) s.publicData
 (NNG_Windows345.window s.proofData 688 58295)
 (UScalar.cast .Usize (s.data.val[1]'(by omega)))=
 NNG_Phases345.firstArgs LIB_Instances.VL LIB_Instances.C
 (NNG_ProjectFrames345.proofData s hd hv) := by
 rw [NNG_ChildSource345.args_fields,NNG_Windows345.bytes,NNG_SplitByte345.value]
 have input : (LIB_Carriers.bytes s.data).getD 1 0=
   byte (s.data.val[1]'(by omega)) := by
  rw [← NNG_DecoderGraph345.bytes]
  exact NNG_ByteGuards345.byte_at s.data.val 1 (by omega)
 change (⟨_,_,_,_⟩ : RSL.TX1_328.Args LIB_Instances.VL)=
  ⟨_,_,_,((LIB_Carriers.bytes s.data).getD 1 0).toNat⟩
 rw [input,byte_nat]
 rfl
#print axioms source
end AspisR1.NNG_FirstArgs345
