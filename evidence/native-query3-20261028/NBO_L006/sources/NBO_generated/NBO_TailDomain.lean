import NBO_QueryFactor
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace NBO_TailDomain
open AspisR1 AspisR1Stage2 Port3_NativeQueryBody
open Port3_PushFrame (bind_success)
def WideCanonical (x : Stage2E) : Prop :=
 NBF_PowerStep.Canonical x.c0 ∧ NBF_PowerStep.Canonical x.c1
/-- Exact lower field-domain statements, not a caller-output equation. -/
structure NBC_Fields (ops : Ops) : Prop where
 product : ∀ x q out, WideCanonical x → NBF_PowerStep.Canonical q →
   ops.op3 x q=ok out → WideCanonical out
 sum : ∀ x y out, WideCanonical x → WideCanonical y →
   ops.op2 x y=ok out → WideCanonical out
 power : NBF_PowerStep.NBC_Qm31Canonical ops
/-- The successful actual constructor supplies rhs canonicality. -/
theorem initial (base : VTop_Stages.Ops) (reserved : Bool)
 (a : verifier.Accumulator)
 (run : (Port3_Initial.install base reserved).op12 .S2=ok (.Ok a)) :
 WideCanonical a.rhs := by
 obtain ⟨_,_,rhs,_,_⟩ := Port3_Initial.accepted_fields base reserved a run
 rw [rhs]
 constructor <;> intro k <;> fin_cases k <;> decide
/-- SAME source-order tail, after the SAME produced basis and rows. The old
power is used for rhs; rho only advances the next power. No returned field
value/canonicality is supplied by the caller. -/
theorem accumulate (ops : Ops) (fields : NBC_Fields ops)
 (p : verifier.Prepared) (a out : verifier.Accumulator) (node : U32)
 (value : Stage2E) (b bout : verifier.BatchedWeights)
 (size : a.weights.val.length=64)
 (progress : S7JoinRowsTrace.Progress b.terms.val 0 (Port3_RowsInstall.toBW b))
 (power : NBF_PowerStep.Canonical a.power)
 (rho : NBF_PowerStep.Canonical p.rho)
 (rhs : WideCanonical a.rhs) (input : WideCanonical value)
 (run : verifier.accumulate_batched_with_node (NBF_Accumulate.install ops)
   p a node value b=ok (out,bout)) :
 WideCanonical out.rhs ∧ NBF_PowerStep.Canonical out.power := by
 obtain ⟨basis,mid,hbasis,hrows,terms,len,phase,body⟩ := NBF_Accumulate.rows
   ops p a node value b size progress power
 rw [body] at run
 simp only [lift,bind_tc_ok] at run
 obtain ⟨product,hproduct,run⟩ := bind_success _ _ _ run
 obtain ⟨sum,hsum,run⟩ := bind_success _ _ _ run
 obtain ⟨marked,hmarked,run⟩ := bind_success _ _ _ run
 obtain ⟨nextPower,hpower,run⟩ := bind_success _ _ _ run
 cases Result.ok.inj run
 exact ⟨fields.sum a.rhs product sum rhs
   (fields.product value a.power product input power hproduct) hsum,
   fields.power a.power p.rho nextPower power rho hpower⟩
#print axioms initial
#print axioms accumulate
end NBO_TailDomain
