import FJg_DigitLoop
import FJf_PointOuterBody
import FJf_RawPointFrame
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJg_PointProvenance
open Aeneas Aeneas.Std Result ControlFlow
open FJf_PointBody (Factors Points)
open FJg_DigitProvenance (cell Source)
abbrev State := FIo_RangeNext.Range × Factors

def Complete (points : Points) (f : Factors) (n : Nat) : Prop :=
  ∀ k : Usize,k.val < n → FJg_DigitLoop.Complete points k f 5

def Inv (points : Points) (t : State) : Prop :=
  t.1.end.val=3 ∧ t.1.start.val≤3 ∧ Complete points t.2 t.1.start.val

def measure (t : State) : Nat := t.1.end.val-t.1.start.val

theorem step (points : Points) (t : State) (inv : Inv points t)
    (out : ControlFlow State Factors)
    (run : FIn_WeightsExtract.weights_new_loop0.body points t.1 t.2=ok out) :
    match out with
    | .done f => Complete points f 3
    | .cont next => Inv points next ∧ measure next < measure t := by
  rcases t with ⟨iter,f⟩
  dsimp only [Inv] at inv
  rcases inv with ⟨he,hs,hv⟩
  cases out with
  | done result =>
    obtain ⟨stop,rfl⟩ := FJf_PointOuterBody.done points iter f result run
    have eq : iter.start.val=3 := by omega
    simpa only [eq] using hv
  | cont next =>
    rcases next with ⟨cursor,next⟩
    obtain ⟨k,hn,hinner⟩ := FJf_PointOuterBody.cont points iter cursor f next run
    have pr := FIo_RangeNext.some_next iter cursor k hn
    have current := FJg_DigitLoop.five points k f next hinner
    dsimp only [Inv]
    refine ⟨⟨by rw [pr.2.1];exact he,by omega,?_⟩,?_⟩
    · intro j hj
      by_cases eq : j=k
      · subst j;exact current
      · have ne : k.val≠j.val := by intro eqv;exact eq (UScalar.ext eqv.symm)
        have frame := FJf_RawPointFrame.loop points k j.val ne _ f next hinner
        intro d hd
        obtain ⟨digit,hcell,hsource⟩ := hv j (by rw [pr.1] at *;omega) d hd
        refine ⟨digit,?_,hsource⟩
        unfold cell
        rw [frame]
        exact hcell
    · simp only [measure,pr.2.1,pr.2.2.1];omega

theorem three (points : Points) (f out : Factors)
    (run : FIn_WeightsExtract.weights_new_loop0 {start:=0#usize,«end»:=3#usize}
      points f=ok out) : Complete points out 3 := by
  exact FIo_LoopInvariant.preserve
    (fun t : State=>FIn_WeightsExtract.weights_new_loop0.body points t.1 t.2)
    (Inv points) (fun f=>Complete points f 3) measure
    (fun t h r hr=>by cases r <;> exact step points t h _ hr)
    ({start:=0#usize,«end»:=3#usize},f) out
    ⟨rfl,by change (0:Nat)≤3;decide,by intro k hk;change k.val<0 at hk;omega⟩ run
#print axioms step
#print axioms three
end AspisR1.FJg_PointProvenance
end
