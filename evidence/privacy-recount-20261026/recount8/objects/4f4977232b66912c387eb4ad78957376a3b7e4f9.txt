import R1Z.ProverRwOuterTag
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwOuterPrepare
open Aeneas Aeneas.Std Result ProverRwFull

def direct (val : alloc.vec.Vec U8) (variant : transport.Variant)
    (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (nonce : Array U8 32#usize) :
    Result (aspis_core.state_only_hiding.StateOnlyHidingContext × Array U8 32#usize) := do
  let s := alloc.vec.Vec.deref val
  let s1 ← Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ s ]))
  let a ← hash s1
  let a1 := nonce
  let context := ProverRwOuterContextModel.context a a1
  let s2 ←
    Aeneas.Std.lift (Array.to_slice
      (Array.make 30#usize [
        85#u8, 78#u8, 80#u8, 82#u8, 79#u8, 86#u8, 69#u8, 68#u8, 58#u8, 82#u8,
        49#u8, 58#u8, 80#u8, 51#u8, 58#u8, 80#u8, 82#u8, 73#u8, 86#u8, 65#u8,
        84#u8, 69#u8, 45#u8, 65#u8, 84#u8, 84#u8, 69#u8, 77#u8, 80#u8, 84#u8
        ]))
  let s3 := alloc.vec.Vec.deref val
  let i := ProverRwOuterTag.byte variant
  let s4 ← Aeneas.Std.lift (Array.to_slice (Array.make 1#usize [ i ]))
  let a2 := ProverRwOuterEncode.value context
  let s5 ← Aeneas.Std.lift (Array.to_slice a2)
  let s6 ← Aeneas.Std.lift (Array.to_slice (Array.make 4#usize [ s2, s3, s4, s5 ]))
  let binding ← hash s6
  ok (context,binding)

variable [ExternalTypes]
/-- Exact actual public prefix with all three source leaves discharged. Both
hash calls, their ordered arguments, and their failure/divergence remain. -/
theorem prepare_direct (ops : ExternalFuns) (val : alloc.vec.Vec U8)
    (v : transport.Variant) (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (nonce : Array U8 32#usize) :
    @ProverRwOuterPrefix.prepare _ (ProverRwOuterTag.selected ops) val v hash nonce =
      direct val v hash nonce := by
  unfold ProverRwOuterPrefix.prepare direct
  simp only [ProverRwOuterTag.construct_installed,ProverRwOuterTag.tag_installed,
    ProverRwOuterTag.encode_installed,bind_tc_ok]

#print axioms prepare_direct
end R1Z.ProverRwOuterPrepare
