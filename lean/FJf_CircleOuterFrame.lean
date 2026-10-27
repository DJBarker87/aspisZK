import FJf_CircleOuterBody
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJf_CircleOuterFrame
open Aeneas Aeneas.Std Result ControlFlow
open FJf_PointBody (Factors)
open FJf_CircleOuterBody (Z)
open FJf_FactorArray (value)
abbrev State := FIo_RangeNext.Range × Factors

def Inv (base : Factors) (j : Nat) (t : State) : Prop :=
  t.1.end.val=2 ∧ t.1.start.val≤2 ∧ ∀ d s,value t.2 j d s=value base j d s

def measure (t : State) : Nat := t.1.end.val-t.1.start.val

theorem step (z : Z) (j : Nat) (hj : j < 3) (base : Factors) (t : State)
    (inv : Inv base j t) (out : ControlFlow State Factors)
    (run : FIn_WeightsExtract.weights_new_loop1.body z t.1 t.2=ok out) :
    match out with
    | .done f => ∀ d s,value f j d s=value base j d s
    | .cont next => Inv base j next ∧ measure next < measure t := by
  rcases t with ⟨iter,factors⟩
  dsimp only [Inv] at inv
  cases out with
  | done f =>
    obtain ⟨_,rfl⟩ := FJf_CircleOuterBody.done z iter factors f run
    exact inv.2.2
  | cont next =>
    rcases next with ⟨cursor,f⟩
    obtain ⟨k,row,updated,back,digit,x,hn,hr,hu,hf⟩ :=
      FJf_CircleOuterBody.cont z iter cursor factors f run
    have pr := FIo_RangeNext.some_next iter cursor k hn
    have hk : k.val < 2 := by rw [pr.1];omega
    obtain ⟨readRow,eb⟩ := FJf_ArrayOps.index_mut factors _ row back hr
    have fr := FJf_CircleFrame.loop k hk j hj _ (back updated) f x hf
    have ne : (Usize.wrapping_add 3#usize k).val≠j := by
      rw [FJf_CircleIndex.value k hk];omega
    dsimp only [Inv]
    refine ⟨⟨by rw [pr.2.1];exact inv.1,by omega,?_⟩,?_⟩
    · intro d s
      rw [fr d s,eb,FJf_FactorArray.outer_set factors _ row updated readRow j d s,if_neg ne]
      exact inv.2.2 d s
    · simp only [measure,pr.2.1,pr.2.2.1];have := pr.2.2.2;omega

theorem two (z : Z) (j : Nat) (hj : j < 3) (factors out : Factors)
    (run : FIn_WeightsExtract.weights_new_loop1 {start:=0#usize,«end»:=2#usize}
      z factors=ok out) :
    ∀ d s,value out j d s=value factors j d s := by
  exact FIo_LoopInvariant.preserve
    (fun t : State => FIn_WeightsExtract.weights_new_loop1.body z t.1 t.2)
    (Inv factors j) (fun f => ∀ d s,value f j d s=value factors j d s) measure
    (fun t h r hr => by cases r <;> exact step z j hj factors t h _ hr)
    ({start:=0#usize,«end»:=2#usize},factors) out
    ⟨rfl,by change (0:Nat)≤2;decide,by intro d s;rfl⟩ run
#print axioms step
#print axioms two
end AspisR1.FJf_CircleOuterFrame
end
