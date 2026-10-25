import Port9OR_BatchProgress

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port9OR_BatchLoop
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2 CheckpointBytes5Effect
open Port9OR_BatchStep (Indices Values Next Out)

/-- D occurs only in the hash-free chunk predicate's phantom argument.
Leaf/parent digest calls have already become explicit Code.read instructions. -/
theorem body_dictionary (base : Port3_NativeBatchBody.Ops) {Hash : Type}
    (D E : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (proof : Slice U8) (root : Digest) (tree lo n slot : Usize) (keys : Array U64 16#usize)
    (idx : Indices) (val : Values) (d pos : Usize) :
    Port9OR_BatchStep.body base D proof root tree hash lo n slot keys idx val d pos=
      Port9OR_BatchStep.body base E proof root tree hash lo n slot keys idx val d pos := rfl

def code (base : Port3_NativeBatchBody.Ops) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (proof : Slice U8) (root : Digest) (tree lo n slot : Usize) (keys : Array U64 16#usize) :
    Nat → Indices → Values → Usize → Usize → Code Out
  | 0,_,_,_,_ => liftResult .div
  | fuel+1,idx,val,d,pos => do
    let out ← Port9OR_BatchStep.body base D proof root tree hash lo n slot keys idx val d pos
    match out with
    | .done result => pure result
    | .cont (nextIdx,nextVal,nextD,nextPos) =>
      code base D hash proof root tree lo n slot keys fuel nextIdx nextVal nextD nextPos

/-- The bounded interpretation equals the actual native loop on all outcomes.
The source itself proves continuation progress, including duplicate paths.
The count bound is proved at the actual caller, not an acceptance restriction. -/
theorem source (base : Port3_NativeBatchBody.Ops) {Hash : Type}
    (D E : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (proof : Slice U8) (root : Digest) (tree lo n slot : Usize) (keys : Array U64 16#usize)
    (small : n.val<256) (fuel : Nat) (idx : Indices) (val : Values) (d pos : Usize)
    (bound : n.val-pos.val+1≤fuel) :
    erase E hash (code base D hash proof root tree lo n slot keys fuel idx val d pos)=
      Port3_NativeBatchBody.verifier.candidate.batch_tree_loop (Port9OR_BatchStep.ops base)
        E proof root tree idx val hash lo n slot keys d pos := by
  induction fuel generalizing idx val d pos with
  | zero => omega
  | succ fuel ih =>
    unfold Port3_NativeBatchBody.verifier.candidate.batch_tree_loop
    rw [Aeneas.Std.loop.eq_def]
    simp only [code,erase_bind,body_dictionary base D E,Port9OR_BatchStep.source,Aeneas.Std.uncurry]
    cases ran : Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body (Port9OR_BatchStep.ops base)
        E proof root tree hash lo n slot keys idx val d pos with
    | fail e => rfl
    | div => rfl
    | ok out =>
      simp only [bind_tc_ok]
      cases out with
      | done result => rfl
      | cont next =>
        obtain ⟨nextIdx,nextVal,nextD,nextPos⟩ := next
        obtain ⟨active,nextEq⟩ := Port9OR_BatchProgress.advance base E hash proof root tree lo n slot keys
          idx val d pos nextIdx nextVal nextD nextPos ran
        have increment := Port3_Wrapping.increment pos (by change pos.val<n.val at active;omega)
        have nextValue : nextPos.val=pos.val+1 := by rw [nextEq,increment]
        exact ih nextIdx nextVal nextD nextPos (by change pos.val<n.val at active;omega)

#print axioms body_dictionary
#print axioms source
end AspisR1.Port9OR_BatchLoop
end
