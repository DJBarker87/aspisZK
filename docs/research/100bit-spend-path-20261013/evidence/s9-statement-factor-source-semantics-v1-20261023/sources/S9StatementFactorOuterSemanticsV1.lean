import S9StatementFactorInnerSemanticsV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1S9StatementFactorOuterSemanticsV1
open AspisR1S9ConstructorV3Loop2InnerCanonicalV1
open AspisR1S9ConstructorV3StatementCellCanonicalV1
open AspisR1S9ActualWeightsNewBoxNewV3
open AspisR1S9StatementCellD18ProgressV1 AspisR1S9StatementSourceLoopFactsV1
open AspisR1S9FactorTableSemanticsV1 AspisR1S9StatementFactorInnerSemanticsV1

def RowsPrefix (points : StatementPoints) (model : Table) (upto : Nat) : Prop :=
  ∀ (k d i : Usize) (hk : k.val<3) (hd : d.val<5) (hi : i.val<4), k.val<upto →
    model k.val d.val i.val=expected points k.val d hd i.val

def CircleFrame (initial model : Table) : Prop :=
  ∀ kk dd ii, 3≤kk → model kk dd ii=initial kk dd ii

/-- Complete actual statement-factor source phase. All three rows and five
radix-four factors per row have D18 meanings, while rows3/4 retain their
initial meanings for the later circle phase. Every inner call is derived
from the same outer source execution. -/
theorem statement_outer_success_exact
    (points : StatementPoints) (factors out : Factors) (initial : Table)
    (hp : StatementPointsCanonical points) (hm : Meaning factors initial)
    (hloop : weights_new_loop0 {start:=0#usize,«end»:=3#usize} points factors=.ok out) :
    ∃ model, Meaning out model ∧ RowsPrefix points model 3 ∧ CircleFrame initial model := by
  let step : (R × Factors) → Result (ControlFlow (R × Factors) Factors) :=
    fun s => weights_new_loop0.body points s.1 s.2
  let measure : (R × Factors) → Nat := fun s => s.1.end.val-s.1.start.val
  let inv : (R × Factors) → Prop := fun s =>
    s.1.end.val=3 ∧ s.1.start.val≤3 ∧
    ∃ model, Meaning s.2 model ∧ RowsPrefix points model s.1.start.val ∧ CircleFrame initial model
  let post : Factors → Prop := fun f =>
    ∃ model, Meaning f model ∧ RowsPrefix points model 3 ∧ CircleFrame initial model
  have hdone : ∀ s result, inv s → step s=.ok (.done result) → post result := by
    rintro ⟨it,a⟩ result hi hb
    dsimp only [inv] at hi
    rcases hi with ⟨he,hs,model,hmeaning,hprefix,hframe⟩
    obtain ⟨hout,hstop⟩ := outer_done_state_stop points it a result hb
    subst result
    have h3 : it.start.val=3 := by omega
    exact ⟨model,hmeaning,by simpa only [h3] using hprefix,hframe⟩
  have hcont : ∀ s next, inv s → step s=.ok (.cont next) → inv next := by
    rintro ⟨it,a⟩ ⟨itNext,b⟩ hi hb
    dsimp only [inv] at hi
    rcases hi with ⟨he,hs,model,hmeaning,hprefix,hframe⟩
    obtain ⟨k,hnext,hinner⟩ := outer_cont_has_execution points it itNext a b hb
    obtain ⟨hlt,hkEq,hstart,hend⟩ := next_some_progress it itNext k hnext
    have hkval : k.val=it.start.val := congrArg UScalar.val hkEq
    have hk3 : k.val<3 := by omega
    obtain ⟨modelNext,hmNext,hrow,houtside⟩ :=
      statement_inner_success_exact points k a b model hp hmeaning hinner
    refine ⟨?_,?_,modelNext,hmNext,?_,?_⟩
    · simpa only [hend] using he
    · dsimp only; omega
    · intro kk dd ii hkk hdd hii hsmall
      change kk.val < itNext.start.val at hsmall
      by_cases hke : kk.val=k.val
      · have hsame : kk=k := UScalar.eq_of_val_eq hke
        subst kk
        exact hrow dd ii hdd hii hdd
      · rw [houtside kk.val dd.val ii.val hke]
        exact hprefix kk dd ii hkk hdd hii (by omega)
    · intro kk dd ii hlarge
      have hne : kk≠k.val := by omega
      rw [houtside kk dd ii hne]
      exact hframe kk dd ii hlarge
  have hdec : ∀ s next, step s=.ok (.cont next) → measure next<measure s := by
    rintro ⟨it,a⟩ ⟨itNext,b⟩ hb
    obtain ⟨k,hnext,hinner⟩ := outer_cont_has_execution points it itNext a b hb
    obtain ⟨hlt,hk,hstart,hend⟩ := next_some_progress it itNext k hnext
    simp only [measure,hstart,hend]
    omega
  have hinit : inv ({start:=0#usize,«end»:=3#usize},factors) := by
    refine ⟨rfl,by simp,initial,hm,?_,?_⟩
    · intro k d i hk hd hi hsmall
      have h0 : (0#usize).val=0 := rfl
      change k.val<(0#usize).val at hsmall
      rw [h0] at hsmall
      omega
    · intro kk dd ii hlarge; rfl
  have hl : Aeneas.Std.loop step ({start:=0#usize,«end»:=3#usize},factors)=.ok out := hloop
  exact AspisR1S9LoopInvariantPropertyV1.loop_invariant_property step measure inv post
    hdone hcont hdec ({start:=0#usize,«end»:=3#usize},factors) out hinit hl

/-- Concrete entry requires no separate initial table-meaning premise. -/
theorem statement_outer_success_actual_table
    (points : StatementPoints) (factors out : Factors)
    (hp : StatementPointsCanonical points)
    (hloop : weights_new_loop0 {start:=0#usize,«end»:=3#usize} points factors=.ok out) :
    ∃ model, Meaning out model ∧ RowsPrefix points model 3 ∧ CircleFrame (rawTable factors) model :=
  statement_outer_success_exact points factors out (rawTable factors) hp (rawTable_meaning factors) hloop

#print axioms statement_outer_success_exact
#print axioms statement_outer_success_actual_table
end AspisR1S9StatementFactorOuterSemanticsV1
