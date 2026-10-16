import AspisV8R19.MemoizedProgramLaw

set_option autoImplicit false
namespace AspisV8R19.OracleProgramOps
open MemoizedProgramLaw OracleResampling AspisV8PairedCommitment
variable {I J A O R : Type}

def bind (p : Program I A O) (next : O → Program I A R) : Program I A R :=
  match p with
  | .done o => next o
  | .ask i k => .ask i (fun a => bind (k a) next)

theorem eval_bind (p : Program I A O) (next : O → Program I A R) (H : I → A) :
    eval H (bind p next) =
      let first := eval H p
      let second := eval H (next first.2)
      (first.1 ++ second.1,second.2) := by
  induction p with
  | done o => simp [bind,eval]
  | ask i k ih => simp [bind,eval,ih]

def rename (label : I → J) : Program I A O → Program J A O
  | .done o => .done o
  | .ask i k => .ask (label i) (fun a => rename label (k a))

def mapView (label : I → J) (v : View I A O) : View J A O :=
  (v.1.map (fun p => (label p.1,p.2)),v.2)

theorem eval_rename (label : I → J) (H : J → A) (p : Program I A O) :
    eval H (rename label p) = mapView label (eval (H ∘ label) p) := by
  induction p with
  | done o => rfl
  | ask i k ih => simp [rename,eval,mapView,ih,Function.comp_def]

theorem pullback_put [DecidableEq I] [DecidableEq J] (label : I → J)
    (inj : Function.Injective label) (t : Table J A) (i : I) (a : A) :
    (put t (label i) a) ∘ label = put (t ∘ label) i a := by
  funext j
  simp only [put,Function.comp_apply,inj.eq_iff]

theorem lazy_rename [Fintype A] [DecidableEq I] [DecidableEq J]
    (label : I → J) (inj : Function.Injective label) (p : Program I A O)
    (t : Table J A) (observe : View J A O → ℚ) :
    lazyMean (rename label p) t observe =
      lazyMean p (t ∘ label) (fun r => observe (mapView label r)) := by
  induction p generalizing t observe with
  | done o => rfl
  | ask i k ih =>
      cases ht : t (label i) with
      | some a =>
          simp only [rename,lazyMean,ht,Function.comp_apply]
          exact ih a t _
      | none =>
          simp only [rename,lazyMean,ht,Function.comp_apply]
          apply mean_congr
          intro a
          rw [ih a, pullback_put label inj]
          rfl

#print axioms eval_bind
#print axioms eval_rename
#print axioms pullback_put
#print axioms lazy_rename
end AspisV8R19.OracleProgramOps
