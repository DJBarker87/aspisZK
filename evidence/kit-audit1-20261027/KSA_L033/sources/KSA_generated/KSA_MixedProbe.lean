import KSA_Mixed
import FIo_NativeFuns
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace KSA

def emittedMixed : FIo_Native.aspis_core.field.QM31 :=
  ⟨⟨1#u32,0#u32⟩,⟨1#u32,0#u32⟩⟩
def emittedRaw : FIo_Native.aspis_core.field.QM31 :=
  ⟨⟨4294967295#u32,0#u32⟩,⟨4294967295#u32,0#u32⟩⟩
def emittedZero : FIo_Native.aspis_core.field.QM31 :=
  ⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩
def emittedResult : FIo_Native.aspis_core.field.QM31 :=
  ⟨⟨3#u32,1#u32⟩,⟨2#u32,0#u32⟩⟩
#reduce FIo_Native.aspis_core.field.wide_exact.WideExact.mul_qm31
  ⟨emittedMixed,emittedZero⟩ emittedRaw
end KSA
