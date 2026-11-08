import NNG_ParseCall094
import Op3I_ParseLaws
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_ParseSuccess094
open Aeneas Aeneas.Std Result NMT_tx1
/-- The source parse result itself fixes S2 and the exact proof extent before
any initializer or batch call is reached. -/
theorem returned (env : RSL.Env) (proof : Slice U8) (variant : transport.Variant)
 (native : NNG_ParseCall094.call env proof=.ok (.Ok variant)) :
 variant=.S2 ∧ proof.val.length=57607 := by
 unfold NNG_ParseCall094.call at native
 cases run : LIBC_ParseShape.model (LIB_Carriers.bytes proof) env with
 | fail e=>rw [run] at native;cases native
 | div=>rw [run] at native;cases native
 | ok r=>
   rw [run] at native
   cases r with
   | Err e=>cases native
   | Ok source=>
     have parsed : Op3I_Source.verifier.candidate.parse_shape Op3I_Std.ops proof=.ok (.Ok source) := by
      change Op3I_Source.verifier.candidate.parse_shape Op3I_Std.ops
       (LIBC_Bytes.raw (LIB_Carriers.bytes proof))=.ok (.Ok source) at run
      rwa [LIBC_Bytes.from_native] at run
     have facts := Op3I_ParseLaws.source_success proof source parsed
     rcases facts with ⟨rfl,width,_⟩
     have same : variant=.S2 := (core.result.Result.Ok.inj (Result.ok.inj native)).symm
     exact ⟨same,width⟩
#print axioms returned
end AspisR1.NNG_ParseSuccess094
