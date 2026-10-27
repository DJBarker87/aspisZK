import FJf_PointDone
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJf_PointStep
open Aeneas Aeneas.Std Result ControlFlow
open FJf_PointBody (Factors Points)
open FJc_WeightQMBridge (SQ)
open FJf_FactorArray (canon value)
abbrev State := FIo_RangeNext.Range × Factors

def Inv (p : Array SQ 10#usize) (k : Usize) (base : Factors) (t : State) : Prop :=
  canon t.2 ∧ t.1.end.val=5 ∧ t.1.start.val≤5 ∧
  ∀ (j d : Nat) (s : Fin 4),value t.2 j d s.val=
    if k.val=j ∧ d < t.1.start.val then FJf_PointCell.point p d s else value base j d s.val

def Post (p : Array SQ 10#usize) (k : Usize) (base out : Factors) : Prop :=
  canon out ∧ ∀ (j d : Nat) (s : Fin 4),value out j d s.val=
    if k.val=j ∧ d<5 then FJf_PointCell.point p d s else value base j d s.val

def measure (t : State) : Nat := t.1.end.val-t.1.start.val

theorem step (points : Points) (k : Usize) (p : Array SQ 10#usize)
    (hp : Array.index_usize points k=ok p) (hc : FJc_WeightArray.canonical p)
    (base : Factors) (t : State) (inv : Inv p k base t)
    (out : ControlFlow State Factors)
    (run : FIn_WeightsExtract.weights_new_loop0_loop0.body points k t.1 t.2=ok out) :
    match out with
    | .done f => Post p k base f
    | .cont next => Inv p k base next ∧ measure next < measure t := by
  rcases t with ⟨iter,factors⟩
  rcases inv with ⟨hf,he,hs,hv⟩
  cases out with
  | done f =>
    obtain ⟨stop,rfl⟩ := FJf_PointDone.done points k iter factors f run
    have eq : iter.start.val=5 := by omega
    exact ⟨hf,by simpa only [eq] using hv⟩
  | cont next =>
    rcases next with ⟨cursor,f⟩
    obtain ⟨he',hs',hm,hf',hv'⟩ := FJf_PointCell.value_step points k p hp hc iter cursor factors f hf run
    refine ⟨⟨hf',?_,?_,?_⟩,?_⟩
    · rw [he'];exact he
    · omega
    · intro j d s
      rw [hv' j d s]
      by_cases hw : k.val=j ∧ iter.start.val=d
      · rw [if_pos hw,if_pos (by omega)]
      · rw [if_neg hw,hv j d s]
        have eq : (k.val=j ∧ d < iter.start.val) ↔ (k.val=j ∧ d < cursor.start.val) := by omega
        rw [eq]
    · simp only [measure,he',hs'];omega
#print axioms step
end AspisR1.FJf_PointStep
end
