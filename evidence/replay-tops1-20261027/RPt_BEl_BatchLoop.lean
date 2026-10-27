import RPt_BEl_BatchStep
import Port9OR_BatchLoop
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEl_BatchLoop
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2 CheckpointBytes5Effect
open Port9OR_BatchStep (Indices Values Next Out)

/-- Reference loop lowering. Range continuation advances the packed-key cursor;
the final guard executes the actual count/padding/verifier tail. The actual
source caller supplies n+1 fuel with n=10 or12; no bound is guessed by BMC. -/
def code (base : Port3_NativeBatchBody.Ops) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (proof : Slice U8) (root : Digest) (tree lo n slot : Usize) (keys : Array U64 16#usize) :
    Nat → Indices → Values → Usize → Usize → Code Out
  | 0,_,_,_,_ => liftResult .div
  | fuel+1,idx,val,d,pos => do
    let out ← BEl_BatchStep.bodyWith BEl_LeafReference.code base D proof root tree hash lo n slot keys idx val d pos
    match out with
    | .done result => pure result
    | .cont (nextIdx,nextVal,nextD,nextPos) =>
      code base D hash proof root tree lo n slot keys fuel nextIdx nextVal nextD nextPos

/-- Whole loop, all outcomes, every attempted prefix and the same live backend
carrier. The existing source/P6 induction supplies the actual caller's finite
bound; no repeated scratch elimination or large concrete normalization is used. -/
theorem observation {S Hash : Type} (call : SdkC_Source.Parts → S → Result SdkC_Source.Digest × S)
    (base : Port3_NativeBatchBody.Ops) (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (proof : Slice U8) (root : Digest) (tree lo n slot : Usize) (keys : Array U64 16#usize)
    (fuel : Nat) (idx : Indices) (val : Values) (d pos : Usize) :
    BEl_CodeCongr.Equivalent call
      (code base D hash proof root tree lo n slot keys fuel idx val d pos)
      (Port9OR_BatchLoop.code base D hash proof root tree lo n slot keys fuel idx val d pos) := by
  induction fuel generalizing idx val d pos with
  | zero => intro state before; rfl
  | succ fuel ih =>
    simp only [code,Port9OR_BatchLoop.code]
    apply BEl_CodeCongr.bind_both
    · exact BEl_BatchStep.leaf_transport call base D hash proof root tree lo n slot keys idx val d pos
    · intro out
      cases out with
      | done result => intro state before; rfl
      | cont next =>
        obtain ⟨nextIdx,nextVal,nextD,nextPos⟩ := next
        exact ih nextIdx nextVal nextD nextPos

#print axioms observation
end AspisR1.BEl_BatchLoop
end
