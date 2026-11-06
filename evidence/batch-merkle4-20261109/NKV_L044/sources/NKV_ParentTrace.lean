import NKV_ParentSource
set_option autoImplicit false
noncomputable section
namespace NKV_ParentTrace
open Aeneas Aeneas.Std Result
open NKV_StepErasure NKV_ReturnBoundary NKV_ParentSource

abbrev Tree (E : Type) := List E × Step
abbrev Parent (E : Type) := List E × Result Reply

def treeObserve {E : Type} (x : Tree E) := (x.1,reject x.2)
def observe {E : Type} (x : Parent E) := (x.1,NKV_ParentSource.observe x.2)

def next {E : Type} (m : Tree E) (k : Indices → Values → Parent E) : Parent E :=
 match m.2 with
 | .fail e => (m.1,fail e)
 | .div => (m.1,div)
 | .ok (.Err e,_,_) => (m.1,ok (.Err e))
 | .ok (.Ok _,i,v) => let rest:=k i v; (m.1++rest.1,rest.2)

def bindRejected {E : Type} (m : List E × Result (Unit × Indices × Values))
 (k : Indices → Values → List E × Result Unit) : List E × Result Unit :=
 match m.2 with
 | .fail e => (m.1,fail e)
 | .div => (m.1,div)
 | .ok (_,i,v) => let rest:=k i v;(m.1++rest.1,rest.2)

theorem next_observed {E : Type} (m : Tree E) (k : Indices → Values → Parent E) :
 observe (next m k)=bindRejected (treeObserve m) (fun i v => observe (k i v)) := by
 rcases m with ⟨events,result⟩
 cases result with
 | fail e => rfl
 | div => rfl
 | ok out => rcases out with ⟨r,i,v⟩;cases r <;> rfl

/-- Exact full history, not history up to permutation. Callee errors and aborts
return their complete prefix without invoking k. -/
theorem next_congr {E : Type} (m n : Tree E) (f g : Indices → Values → Parent E)
 (head : treeObserve m=treeObserve n)
 (tail : ∀ i v,observe (f i v)=observe (g i v)) :
 observe (next m f)=observe (next n g) := by
 rw [next_observed,next_observed,head]
 congr 1
 funext i v
 exact tail i v

def three {E : Type} (c0 c1 c2 : Indices → Values → Tree E) : Parent E :=
 next (c0 zeroI zeroV) (fun i v => next (c1 i v)
   (fun i v => next (c2 i v) (fun _ _ => ([],ok (.Ok ())))))

theorem three_congr {E : Type} (a0 a1 a2 b0 b1 b2 : Indices → Values → Tree E)
 (first : ∀ i v,treeObserve (a0 i v)=treeObserve (b0 i v))
 (second : ∀ i v,treeObserve (a1 i v)=treeObserve (b1 i v))
 (third : ∀ i v,treeObserve (a2 i v)=treeObserve (b2 i v)) :
 observe (three a0 a1 a2)=observe (three b0 b1 b2) := by
 unfold three
 apply next_congr _ _ _ _ (first _ _)
 intro i v
 apply next_congr _ _ _ _ (second i v)
 intro i v
 apply next_congr _ _ _ _ (third i v)
 intro i v;rfl

theorem first_error {E : Type} (c0 c1 c2 : Indices → Values → Tree E)
 (events : List E) (error : AspisR1Stage2.verifier.Error) (idx : Indices) (val : Values)
 (reply : c0 zeroI zeroV=(events,ok (.Err error,idx,val))) :
 three c0 c1 c2=(events,ok (.Err error)) := by rw [three,reply];rfl

theorem second_error {E : Type} (c0 c1 c2 : Indices → Values → Tree E)
 (first second : List E) (error : AspisR1Stage2.verifier.Error)
 (i0 i1 : Indices) (v0 v1 : Values)
 (reply0 : c0 zeroI zeroV=(first,ok (.Ok (),i0,v0)))
 (reply1 : c1 i0 v0=(second,ok (.Err error,i1,v1))) :
 three c0 c1 c2=(first++second,ok (.Err error)) := by
 rw [three,reply0]
 simp only [next]
 rw [reply1]

set_option pp.proofs false
#print three_congr
#print first_error
#print second_error
#print axioms next_observed
#print axioms next_congr
#print axioms three_congr
#print axioms first_error
#print axioms second_error
end NKV_ParentTrace
end
