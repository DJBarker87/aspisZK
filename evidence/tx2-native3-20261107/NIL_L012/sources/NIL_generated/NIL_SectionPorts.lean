import NIL_FreshOps
set_option autoImplicit false
noncomputable section
namespace NIL_SectionPorts
open Aeneas Aeneas.Std Result NIL_Carriers NIL_ResultTransport NIL_ResultReverse
open AspisR1

theorem semantic (bytes : Slice U8) (start : Usize) :
 outer (NIL_Carriers.inner (fun x=>(array k x.1,x.2)))
  (NIL_FreshOps.semantic bytes start)=CheckpointBytes4Ops.readSemanticAlpha bytes start := by
 unfold NIL_FreshOps.semantic
 apply outer_roundtrip
 intro x
 apply inner_reverse
 intro x;cases x
 simp only [array_roundtrip unK k k_reverse]

theorem weights (bytes : Slice U8) (start : Usize) (v : alloc.vec.Vec Fresh.K) :
 outer (NIL_Carriers.inner (fun x=>(vec k x.1,x.2)))
  (NIL_FreshOps.weights bytes start v)=CheckpointBytes4Ops.readWeights bytes start (vec k v) := by
 unfold NIL_FreshOps.weights
 apply outer_roundtrip
 intro x
 apply inner_reverse
 intro x;cases x
 simp only [vec_roundtrip unK k k_reverse]

theorem validation (q : Array U32 22#usize) :
 outer (NIL_Carriers.inner id) (NIL_FreshOps.validate q)=CheckpointBytes4Ops.validate q := by
 unfold NIL_FreshOps.validate
 apply outer_roundtrip
 intro x
 exact inner_reverse id id (fun _=>rfl) x
#print axioms semantic
#print axioms weights
#print axioms validation
end NIL_SectionPorts
