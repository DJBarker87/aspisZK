import NKU_HeaderStep
import NKU_HeaderPrefix
set_option autoImplicit false
noncomputable section
namespace NKU_FineHeader
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission NJU_ResumeObserved
open NKU_Chronology
/-- The temporary iterator is live in the SAME parent record at occurrence1.
Its scope ends before the digest phase, as in the frozen header expression. -/
def any (s : NKU.State) : Run (Bool × core.slice.iter.Iter U8) :=
 match s.iterator with
 | none => liftM (Result.fail .panic)
 | some it => NJU_Log.record (.headerAny it) (NJJ_Any.any it)
def run {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H) : Stage Unit := fun s=>do
 let prefixReply ← NKU_HeaderPrefix.prefixValue d s.frame.checkpoint .S2
 NKK_Try.emitted prefixReply fun (next,it)=>do
 let live := {s with iterator := some it,decoded := {s.decoded with next := some next}}
 let (hit,returnedIt) ← any live
 let liveOut := {live with iterator := some returnedIt}
 if hit then pure (.Err .Checkpoint) else do
 let «end» ← lift (Std.Usize.wrapping_sub (Slice.len s.frame.checkpoint) 32#usize)
 let afterScope := {liveOut with iterator := s.iterator}
 pure (.Ok ((),NKU.headerPost afterScope next «end»))
theorem installed {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (s : NKU.State) :
 run d s=NKU_HeaderStep.run d s := by
 unfold NKU_HeaderStep.run
 rw [NKU_HeaderPrefix.source]
 unfold run NKU_HeaderPrefix.tail any
 simp only [NKK_LogAlgebra.bind_assoc,NKK_LogReduce.pure_bind,NKK_Try.branch]
 apply NKK_LogAlgebra.bind_congr
 intro reply
 cases reply with
 | Err err => rfl
 | Ok pair =>
  rcases pair with ⟨next,it⟩
  simp only [NKK_LogAlgebra.bind_assoc,NKK_LogReduce.pure_bind,NKK_Try.branch]
  apply NKK_LogAlgebra.bind_congr
  rintro ⟨hit,returnedIt⟩
  cases hit <;> rfl
#print axioms installed
end NKU_FineHeader
