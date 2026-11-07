import NNG_InstalledCalls094
import NNG_PrepareTransport094
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Input094
open Aeneas Aeneas.Std Result NMT_tx1
abbrev Args := RSL.TX1_094.Args LIB_Instances.VL
/-- The row's deployed observer domain is None. All byte slices and public
fields are lowered from the original arguments, and k retains its guard. -/
def input (a : Args) (_obs : RSL.Observer) (env : RSL.Env) : NNG_Context094.Parent Unit :=
 ⟨NNG_PrepareTransport094.digest env,NNG_Carriers094.fromT9 a.public_,LIBC_Bytes.raw a.public_bytes,
  LIBC_Bytes.raw a.proof,LIBC_Usize.raw a.k,(),none⟩
theorem public_extent (a : Args) (obs : RSL.Observer) (env : RSL.Env)
 (hd : RSL.TX1_094.Domain LIB_Instances.VL a obs a.public_) :
 LIB_Carriers.bytes (input a obs env).publicBytes=a.public_bytes := by
 apply LIBC_Bytes.to_native
 rw [hd.2.2]
 change 1880≤Usize.max
 scalar_tac
#print axioms public_extent
end AspisR1.NNG_Input094
