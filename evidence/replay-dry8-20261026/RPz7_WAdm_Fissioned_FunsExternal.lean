import RPz7_WAdm_Fissioned_Types
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace WAdm_Fissioned
/-- Concrete content interpretations of the pure owned standard iterator. -/
def Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter
    {T : Type} {N : Usize} (xs : Aeneas.Std.Array T N) : Result (core.array.iter.IntoIter T N) := ok xs.val

def core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next
    {T : Type} {N : Usize} (xs : core.array.iter.IntoIter T N) :
    Result (Option T × core.array.iter.IntoIter T N) :=
  match xs with | [] => ok (none,[]) | x::tail => ok (some x,tail)

/-- Physical eight-limb LE scalar content. The native source byte contract
is checked separately; no parent/writer output equation enters this body. -/
def aspis_core.field.wide_exact.WideExact.to_le_bytes
    (x : aspis_core.field.wide_exact.WideExact) : Result (Aeneas.Std.Array U8 32#usize) :=
  ok ⟨AspisR1.CheckpointBytesE.rawBytes x,AspisR1.CheckpointBytesE.rawBytes_length x⟩

/-- Retain the existing emitted checked slices and their back-writes. -/
def aspis_core.field.QM31.write_le_bytes (x : aspis_core.field.QM31) (out : Slice U8) : Result (Slice U8) :=
  OraclePortCkptAbi2Extracted.aspis_core.field.QM31.write_le_bytes x out
end WAdm_Fissioned
