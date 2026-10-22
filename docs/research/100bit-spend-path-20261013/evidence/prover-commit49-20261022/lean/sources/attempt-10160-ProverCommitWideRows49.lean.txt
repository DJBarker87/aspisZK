import R1Z.ProverCommitEvaluatorMap49
/-! Concrete raw-row embedding into the existing WideExact R1 functionals. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitWideRows49
open R0P.SemSource R0Z.HonestView AspisR0.Opening
open ProverCommitValueRange47
open scoped BigOperators

local instance : NeZero (2 : E) := ⟨AspisWideTower.wideExact_two_ne_zero⟩

def rows {K : Type} [Field K] (a : Fin 10 → K) (x0 y0 x1 y1 : K) (j : Fin 1024) : Fin 7 → K :=
  ![indicator R0P.copyInactiveRows (AspisR1.rowEquiv.symm j),
    eqWeight (openingPoints a 0) (AspisR1.rowEquiv.symm j),
    eqWeight (openingPoints a 1) (AspisR1.rowEquiv.symm j),
    eqWeight (openingPoints a 2) (AspisR1.rowEquiv.symm j),
    libraWeight a j,
    ProverCommitEval47.messageEval (Pi.single j 1) x0 y0,
    ProverCommitEval47.messageEval (Pi.single j 1) x1 y1]

theorem map_seven {A B : Type} (f : A → B) (a b c d e x y : A) (k : Fin 7) :
    f (![a,b,c,d,e,x,y] k)=![f a,f b,f c,f d,f e,f x,f y] k := by
  fin_cases k <;> rfl

theorem point_map {K L : Type} [Field K] [Field L] (f : K →+* L)
    (a : Fin 10 → K) (i : Fin 3) (r : Fin 1024) :
    f (eqWeight (openingPoints a i) r)=eqWeight (openingPoints (fun b => f (a b)) i) r := by
  rw [ProverCommitWeightMap49.eq_map]
  apply congrArg (fun p => eqWeight p r)
  funext b
  exact ProverCommitWeightMap49.opening_map f a i b

theorem rows_map {K L : Type} [Field K] [Field L] (f : K →+* L)
    (a : Fin 10 → K) (x0 y0 x1 y1 : K) (j : Fin 1024) (k : Fin 7) :
    f (rows a x0 y0 x1 y1 j k)=rows (fun i => f (a i)) (f x0) (f y0) (f x1) (f y1) j k := by
  unfold rows
  rw [map_seven f]
  rw [ProverCommitWeightMap49.indicator_map,point_map f a 0,point_map f a 1,point_map f a 2,
    ProverCommitWeightMap49.libra_map,ProverCommitEvaluatorMap49.message_single_map,
    ProverCommitEvaluatorMap49.message_single_map]

theorem embed_rows (a : Fin 10 → Q) (x0 y0 x1 y1 : Q) (j : Fin 1024) (k : Fin 7) :
    embed (ProverCommitRawSource49.model a x0 y0 x1 y1 j k)=
      rows (fun i => embed (a i)) (embed x0) (embed y0) (embed x1) (embed y1) j k := by
  change embed (rows a x0 y0 x1 y1 j k)=_
  exact rows_map (algebraMap Q E) a x0 y0 x1 y1 j k

theorem rows_model (ch : Challenges E) (j : Fin 1024) (k : Fin 7) :
    rows (alpha ch) (ch.circle 0).1.1 (ch.circle 0).1.2 (ch.circle 1).1.1 (ch.circle 1).1.2 j k=
      R1Z.Batched.ell AspisR1.rowEquiv ch k (Pi.single j 1) :=
  ProverCommitRawCoefficient49.model_eq_ell _ _ _ _

theorem weighted_rows (ch : Challenges E) (j : Fin 1024) :
    (∑ k : Fin 7, ch.opening 1^k.val*rows (alpha ch) (ch.circle 0).1.1 (ch.circle 0).1.2
      (ch.circle 1).1.1 (ch.circle 1).1.2 j k)=R1Z.Batched.weightsR1 AspisR1.rowEquiv ch j := by
  simp only [rows_model,R1Z.Batched.weightsR1,R1Z.BatchedAlgebra.weightsOf]

#print axioms map_seven
#print axioms point_map
#print axioms rows_map
#print axioms embed_rows
#print axioms rows_model
#print axioms weighted_rows
end R1Z.ProverCommitWideRows49
