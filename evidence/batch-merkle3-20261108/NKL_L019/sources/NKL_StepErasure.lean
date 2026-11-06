import NKL_ExplicitBody
set_option autoImplicit false
noncomputable section
namespace NKL_StepErasure
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2

def mapResult {A B : Type} (f : A → B) : Result A → Result B
 | .ok x => .ok (f x) | .fail e => .fail e | .div => .div

theorem map_ok {A B : Type} (f : A → B) (x : A) :
 mapResult f (ok x)=ok (f x) := rfl

theorem map_bind {A B C : Type} (f : B → C) (m : Result A) (k : A → Result B) :
 mapResult f (m >>= k) = (m >>= fun x => mapResult f (k x)) := by cases m <;> rfl

theorem map_ite {A B : Type} (f : A → B) (p : Prop) [Decidable p] (a b : Result A) :
 mapResult f (if p then a else b) = if p then mapResult f a else mapResult f b := by split <;> rfl

theorem map_pair {A B C D : Type} (f : C → D) (p : A × B) (k : A → B → Result C) :
 mapResult f (match p with | (a,b) => k a b) =
 (match p with | (a,b) => mapResult f (k a b)) := by cases p; rfl

theorem map_cf {A B C D : Type} (f : C → D)
 (cf : core.ops.control_flow.ControlFlow A B) (cont : B → Result C) (stop : A → Result C) :
 mapResult f (match cf with | .Continue b => cont b | .Break a => stop a) =
 (match cf with | .Continue b => mapResult f (cont b) | .Break a => mapResult f (stop a)) := by
 cases cf <;> rfl

abbrev Indices := Array U32 16#usize
abbrev Values := Array (Array U8 32#usize) 16#usize
abbrev State := Indices × Values × Usize × Usize
abbrev Reply := core.result.Result Unit verifier.Error

def erase : ControlFlow State (Indices × Values × (Reply × Bool)) →
 ControlFlow State (Indices × Values × Option Reply)
 | .cont state => .cont state
 | .done (idx,val,r,lost) => .done (idx,val,if lost then none else some r)

/-- One full source-order iteration/tail. This is a parametric body equality,
not a positive deployed root; the dictionary and native cut installation must
be discharged separately. The explicit Result is retained before erasure. -/
theorem source (ops : AspisR1.Port3_NativeBatchBody.Ops)
 {H : Type} (D : aspis_core.digest.Digest32 H)
 (proof : Slice U8) (root : Array U8 32#usize) (tree : Usize) (hash : H)
 (lo n s : Usize) (keys : Array U64 16#usize) (idx : Indices) (val : Values)
 (d pos : Usize) :
 mapResult erase (NKL_ExplicitBody.verifier.candidate.batch_tree_loop.body
  ops D proof root tree hash lo n s keys idx val d pos) =
 AspisR1.Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
  ops D proof root tree hash lo n s keys idx val d pos := by
 unfold NKL_ExplicitBody.verifier.candidate.batch_tree_loop.body
  AspisR1.Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
 simp only [map_bind,map_ite,map_pair,map_cf,map_ok,erase]
 by_cases active : pos<n
 · simp only [if_pos active]
   rfl
 · simp only [if_neg active]
   congr 1
   funext front
   congr 1
   funext counted
   congr 1
   funext converted
   congr 1
   funext branched
   cases branched with
   | Break residual =>
     simp only [map_bind,map_ok,erase,ite_true]
   | Continue count =>
     simp only [map_bind,map_ite,map_pair,map_cf,map_ok,erase,ite_true,ite_false]
     congr 1
     funext nodes
     congr 1
     funext caps
     congr 1
     funext cap
     by_cases limit : count>cap
     · simp only [if_pos limit]
     · simp only [if_neg limit]
       congr 1
       funext scaled
       congr 1
       funext suffix
       congr 1
       funext chunks
       congr 1
       funext pair
       rcases pair with ⟨bad,iterator⟩
       try simp only [map_ite,map_bind,map_ok,erase,ite_true,ite_false]
       cases bad with
       | true => rfl
       | false =>
         try simp only [Bool.false_eq_true,if_false,map_bind]
         congr 1
         funext scaled2
         congr 1
         funext supplied
         congr 1
         funext triple
         rcases triple with ⟨valid,afterIdx,afterVal⟩
         cases valid <;> rfl

set_option pp.proofs false
#print source
#print axioms map_ok
#print axioms map_bind
#print axioms map_ite
#print axioms map_pair
#print axioms map_cf
#print axioms source
end NKL_StepErasure
end
