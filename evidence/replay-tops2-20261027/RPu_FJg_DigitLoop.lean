import RPu_FJg_DigitProvenance
import RPu_FJf_PointDone
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJg_DigitLoop
open Aeneas Aeneas.Std Result ControlFlow
open FJf_PointBody (Factors Points)
open FJg_DigitProvenance (cell Source)
abbrev State := FIo_RangeNext.Range × Factors

def Complete (points : Points) (k : Usize) (f : Factors) (n : Nat) : Prop :=
  ∀ d,d < n → ∃ digit,cell f k.val d=some digit ∧ Source points k.val d digit

def Inv (points : Points) (k : Usize) (t : State) : Prop :=
  t.1.end.val=5 ∧ t.1.start.val≤5 ∧ Complete points k t.2 t.1.start.val

def measure (t : State) : Nat := t.1.end.val-t.1.start.val

theorem step (points : Points) (k : Usize) (t : State) (inv : Inv points k t)
    (out : ControlFlow State Factors)
    (run : FIn_WeightsExtract.weights_new_loop0_loop0.body points k t.1 t.2=ok out) :
    match out with
    | .done f => Complete points k f 5
    | .cont next => Inv points k next ∧ measure next < measure t := by
  rcases t with ⟨iter,f⟩
  dsimp only [Inv] at inv
  rcases inv with ⟨he,hs,hv⟩
  cases out with
  | done result =>
    obtain ⟨stop,rfl⟩ := FJf_PointDone.done points k iter f result run
    have eq : iter.start.val=5 := by omega
    simpa only [eq] using hv
  | cont next =>
    rcases next with ⟨cursor,next⟩
    obtain ⟨he',hs',more,current,frame⟩ := FJg_DigitProvenance.step points k iter cursor f next run
    dsimp only [Inv]
    refine ⟨⟨by rw [he'];exact he,by omega,?_⟩,?_⟩
    · intro d hd
      by_cases eq : d=iter.start.val
      · simpa only [eq] using current
      · obtain ⟨digit,hcell,hsource⟩ := hv d (by omega)
        exact ⟨digit,(frame k.val d (Or.inr eq)).trans hcell,hsource⟩
    · simp only [measure,he',hs'];omega

theorem five (points : Points) (k : Usize) (f out : Factors)
    (run : FIn_WeightsExtract.weights_new_loop0_loop0 {start:=0#usize,«end»:=5#usize}
      points f k=ok out) : Complete points k out 5 := by
  exact FIo_LoopInvariant.preserve
    (fun t : State=>FIn_WeightsExtract.weights_new_loop0_loop0.body points k t.1 t.2)
    (Inv points k) (fun f=>Complete points k f 5) measure
    (fun t h r hr=>by cases r <;> exact step points k t h _ hr)
    ({start:=0#usize,«end»:=5#usize},f) out
    ⟨rfl,by change (0:Nat)≤5;decide,by intro d hd;change d<0 at hd;omega⟩ run
#print axioms step
#print axioms five
end AspisR1.FJg_DigitLoop
end
