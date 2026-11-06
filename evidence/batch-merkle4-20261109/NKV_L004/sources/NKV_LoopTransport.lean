import NKV_StepErasure
set_option autoImplicit false
noncomputable section
namespace NKV_LoopTransport
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2
open NKV_StepErasure

/-- Finite source-ordered execution of arbitrary single-step cuts. The stopped
child's fail/div is retained; a next cut is present only after cont. This is a
support induction interface, not an admissible deployed-root hypothesis. -/
inductive Walk {S O : Type} (body : S → Result (ControlFlow S O)) :
 S → Result O → Prop where
 | done (s : S) (o : O) (step : body s=ok (.done o)) : Walk body s (ok o)
 | failed (s : S) (e : Error) (step : body s=fail e) : Walk body s (fail e)
 | diverged (s : S) (step : body s=div) : Walk body s div
 | next (s t : S) (out : Result O) (step : body s=ok (.cont t))
     (tail : Walk body t out) : Walk body s out

theorem execute {S O : Type} (body : S → Result (ControlFlow S O))
 (s : S) (out : Result O) (walk : Walk body s out) : loop body s=out := by
 induction walk with
 | done s o step => rw [loop.eq_def,step]
 | failed s e step => rw [loop.eq_def,step]
 | diverged s step => rw [loop.eq_def,step]
 | next s t out step tail ih => rw [loop.eq_def,step];exact ih

def mapFlow {S O P : Type} (f : O → P) : ControlFlow S O → ControlFlow S P
 | .cont s => .cont s | .done o => .done (f o)

/-- Source-ordered induction, including the first stopping step, not equality
of independently chosen loop endpoints. -/
theorem transport {S O P : Type} (f : O → P)
 (body : S → Result (ControlFlow S O)) (target : S → Result (ControlFlow S P))
 (same : ∀ s,mapResult (mapFlow f) (body s)=target s)
 (s : S) (out : Result O) (walk : Walk body s out) :
 Walk target s (mapResult f out) := by
 induction walk with
 | done s o step =>
   apply Walk.done
   rw [←same s,step];rfl
 | failed s e step =>
   apply Walk.failed
   rw [←same s,step];rfl
 | diverged s step =>
   apply Walk.diverged
   rw [←same s,step];rfl
 | next s t out step tail ih =>
   apply Walk.next s t _ _ ih
   rw [←same s,step];rfl

abbrev Out := Indices × Values × (Reply × Bool)
abbrev CohortOut := Indices × Values × Option Reply

def eraseOut : Out → CohortOut
 | (idx,val,r,lost) => (idx,val,if lost then none else some r)

theorem erase_flow (x : ControlFlow State Out) : erase x=mapFlow eraseOut x := by
 cases x with
 | cont s => rfl
 | done o => rcases o with ⟨i,v,r,b⟩;rfl

/-- Both concrete loop bodies on the SAME physical input and pre-state. Ops
remains explicit only in this support theorem; no row root is claimed. -/
theorem source (ops : AspisR1.Port3_NativeBatchBody.Ops)
 {H : Type} (D : aspis_core.digest.Digest32 H)
 (proof : Slice U8) (root : Array U8 32#usize) (tree : Usize) (hash : H)
 (lo n slot : Usize) (keys : Array U64 16#usize) (s : State) (out : Result Out)
 (walk : Walk (fun (i,v,d,p) => NKV_FRef.verifier.candidate.batch_tree_loop.body
   ops D proof root tree hash lo n slot keys i v d p) s out) :
 Aeneas.Std.loop (fun (i,v,d,p) =>
  AspisR1.Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
   ops D proof root tree hash lo n slot keys i v d p) s=mapResult eraseOut out := by
 apply execute
 apply transport eraseOut _ _ _ s out walk
 intro state
 rcases state with ⟨i,v,d,p⟩
 rw [←NKV_StepErasure.source ops D proof root tree hash lo n slot keys i v d p]
 congr 1
 funext flow
 exact (erase_flow flow).symm

set_option pp.proofs false
#print source
#print axioms execute
#print axioms transport
#print axioms erase_flow
#print axioms source
end NKV_LoopTransport
end
