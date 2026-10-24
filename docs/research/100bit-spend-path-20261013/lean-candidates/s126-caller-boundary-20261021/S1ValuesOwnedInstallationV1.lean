import S1ValuesOwnedFrameV1
import CurrentCompactCallerModelV1
set_option autoImplicit false
namespace AspisS1ValuesOwnedInstallation
open Aeneas Aeneas.Std Result

/-- Content-preserving owned snapshots. Heap reservation and SDK borrows are
not modeled by this conversion; the reference owns both complete buffers. -/
def toVec (bytes : Slice U8) : alloc.vec.Vec U8 := ⟨bytes.val,bytes.property⟩
def toSlice (bytes : alloc.vec.Vec U8) : Slice U8 := ⟨bytes.val,bytes.property⟩

def expandValues (input output : Slice U8) :
    Result ((core.result.Result Unit AspisR1CurrentCaller.compact.CodecError) × Slice U8) := do
  let (status,_,updated) ← AspisS1ValuesOwned.values_owned_reference (toVec input) (toVec output)
  ok (status,toSlice updated)

theorem length_frame (input output updated : Slice U8)
    (status : core.result.Result Unit AspisR1CurrentCaller.compact.CodecError)
    (call : expandValues input output=ok (status,updated)) :
    updated.length=output.length := by
  unfold expandValues at call
  cases source : AspisS1ValuesOwned.values_owned_reference (toVec input) (toVec output) with
  | fail e => simp only [source] at call; cases call
  | div => simp only [source] at call; cases call
  | ok result =>
    rcases result with ⟨status1,next,out⟩
    simp only [source,bind_tc_ok] at call
    have same := congrArg Prod.snd (Result.ok.inj call)
    change toSlice out=updated at same
    subst updated
    exact (AspisS1ValuesOwnedFrame.reference_frame _ _ _ _ _ source).2

def withValues (ops : AspisR1CurrentCaller.Ops) : AspisR1CurrentCaller.Ops :=
  {ops with op11:=expandValues}

/-- Both compact semantic expansion and Y1 use this same complete reference. -/
def nativeValues : AspisS1NativeCompact.Ops := {expandValues:=expandValues}

#print axioms expandValues
#print axioms length_frame
end AspisS1ValuesOwnedInstallation
