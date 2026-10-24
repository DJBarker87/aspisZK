import S9StatementCellD18ProgressV1
import S9StatementSourceLoopFactsV1
import S9LoopInvariantPropertyV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1S9StatementFactorInnerSemanticsV1
open AspisR1S9ConstructorV3Loop2InnerCanonicalV1
open AspisR1S9ConstructorV3StatementCellCanonicalV1
open AspisR1S9ActualWeightsNewBoxNewV3
open AspisR1S9StatementCellD18ProgressV1 AspisR1S9StatementSourceLoopFactsV1
open AspisR1S9FactorTableSemanticsV1

def RowPrefix (points : StatementPoints) (model : Table) (k upto : Nat) : Prop :=
  ∀ (d i : Usize) (hd : d.val<5) (hi : i.val<4), d.val<upto →
    model k d.val i.val=expected points k d hd i.val

def Outside (initial model : Table) (k : Nat) : Prop :=
  ∀ kk dd ii, kk≠k → model kk dd ii=initial kk dd ii

/-- Entire actual source d=0..4 loop: all five stored cells obtain the
retained D18 bilinear meanings, and every other row remains exactly framed.
No canonicality/meaning premise is imposed on old factor contents. -/
theorem statement_inner_success_exact
    (points : StatementPoints) (k : Usize) (factors out : Factors) (initial : Table)
    (hp : StatementPointsCanonical points) (hm : Meaning factors initial)
    (hloop : weights_new_loop0_loop0 {start:=0#usize,«end»:=5#usize}
      points factors k=.ok out) :
    ∃ model, Meaning out model ∧ RowPrefix points model k.val 5 ∧ Outside initial model k.val := by
  let step : (R × Factors) → Result (ControlFlow (R × Factors) Factors) :=
    fun s => weights_new_loop0_loop0.body points k s.1 s.2
  let measure : (R × Factors) → Nat := fun s => s.1.end.val-s.1.start.val
  let inv : (R × Factors) → Prop := fun s =>
    s.1.end.val=5 ∧ s.1.start.val≤5 ∧
    ∃ model, Meaning s.2 model ∧ RowPrefix points model k.val s.1.start.val ∧ Outside initial model k.val
  let post : Factors → Prop := fun f =>
    ∃ model, Meaning f model ∧ RowPrefix points model k.val 5 ∧ Outside initial model k.val
  have hdone : ∀ s result, inv s → step s=.ok (.done result) → post result := by
    rintro ⟨it,a⟩ result hi hb
    dsimp only [inv] at hi
    rcases hi with ⟨he,hs,model,hmeaning,hprefix,houtside⟩
    obtain ⟨hout,hstop⟩ := inner_done_state_stop points k it a result hb
    subst result
    have h5 : it.start.val=5 := by omega
    exact ⟨model,hmeaning,by simpa only [h5] using hprefix,houtside⟩
  have hcont : ∀ s next, inv s → step s=.ok (.cont next) → inv next := by
    rintro ⟨it,a⟩ ⟨itNext,b⟩ hi hb
    dsimp only [inv] at hi
    rcases hi with ⟨he,hs,model,hmeaning,hprefix,houtside⟩
    obtain ⟨d,hd,hnext,hmNext⟩ := actual_statement_cell_d18_progress
      points k it itNext a b model hp hmeaning he hb
    obtain ⟨hlt,hdEq,hstart,hend⟩ := next_some_progress it itNext d hnext
    have hdval : d.val=it.start.val := congrArg UScalar.val hdEq
    refine ⟨?_,?_,write model k.val d.val (expected points k.val d hd),hmNext,?_,?_⟩
    · simpa only [hend] using he
    · dsimp only; omega
    · intro dd ii hdd hii hsmall
      by_cases hde : dd.val=d.val
      · have hsame : dd=d := UScalar.eq_of_val_eq hde
        subst dd
        simp only [write,if_pos rfl]
      · simp only [write,if_pos rfl,if_neg hde]
        exact hprefix dd ii hdd hii (by omega)
    · intro kk dd ii hne
      simp only [write,if_neg hne]
      exact houtside kk dd ii hne
  have hdec : ∀ s next, step s=.ok (.cont next) → measure next<measure s := by
    rintro ⟨it,a⟩ ⟨itNext,b⟩ hb
    obtain ⟨d,hnext⟩ := inner_cont_has_next points k it itNext a b hb
    obtain ⟨hlt,hd,hstart,hend⟩ := next_some_progress it itNext d hnext
    simp only [measure,hstart,hend]
    omega
  have hinit : inv ({start:=0#usize,«end»:=5#usize},factors) := by
    refine ⟨rfl,by simp,initial,hm,?_,?_⟩
    · intro d i hd hi hsmall
      have h0 : (0#usize).val=0 := rfl
      change d.val<(0#usize).val at hsmall
      rw [h0] at hsmall
      omega
    · intro kk dd ii hne; rfl
  have hl : Aeneas.Std.loop step ({start:=0#usize,«end»:=5#usize},factors)=.ok out := hloop
  exact AspisR1S9LoopInvariantPropertyV1.loop_invariant_property step measure inv post
    hdone hcont hdec ({start:=0#usize,«end»:=5#usize},factors) out hinit hl

#print axioms statement_inner_success_exact
end AspisR1S9StatementFactorInnerSemanticsV1
