import FJr_CircleInnerWrite
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJr_CircleInnerLoop
open Aeneas Aeneas.Std Result ControlFlow
open FJc_WeightQMBridge (SQ)
open FJc_WeightValues (Canon decode)
open FJf_PointBody (Factors)
open FJf_FactorArray (canon value)
abbrev FK := OraclePortCheckpointAbiC5.K
abbrev State := FIo_RangeNext.Range × Factors × SQ

def advance (x : FK) : Nat → FK
  | 0=>x
  | n+1=>FJd_LoopReference.double (FJd_LoopReference.double (advance x n))

def model (seed : FK) (base : Factors) (k count j d : Nat) (s : Fin 4) : FK :=
  if k=j ∧ 1≤d ∧ d<count then
    FJr_CircleInnerCell.quad (advance seed (d-1))
      (FJd_LoopReference.double (advance seed (d-1))) s
  else value base j d s.val

def Inv (seed : FK) (base : Factors) (k : Nat) (t : State) : Prop :=
  t.1.end.val=5 ∧ 1≤t.1.start.val ∧ t.1.start.val≤5 ∧
  Canon t.2.2 ∧ decode t.2.2=advance seed (t.1.start.val-1) ∧ canon t.2.1 ∧
  ∀ j d s,value t.2.1 j d s.val=model seed base k t.1.start.val j d s

def Post (seed : FK) (base : Factors) (k : Nat) (out : Factors) : Prop :=
  canon out ∧ ∀ j d s,value out j d s.val=model seed base k 5 j d s

def measure (t : State) : Nat := t.1.end.val-t.1.start.val

theorem step (k : Usize) (hk : k.val < 2) (seed : FK) (base : Factors)
    (t : State) (inv : Inv seed base (3+k.val) t) (result : ControlFlow State Factors)
    (run : FIn_WeightsExtract.weights_new_loop1_loop0.body k t.1 t.2.1 t.2.2=ok result) :
    match result with
    | .done out=>Post seed base (3+k.val) out
    | .cont next=>Inv seed base (3+k.val) next ∧ measure next < measure t := by
  rcases t with ⟨iter,factors,x⟩
  rcases inv with ⟨he,hlo,hhi,cx,vx,hf,values⟩
  change iter.end.val=5 at he
  change 1≤iter.start.val at hlo
  change iter.start.val≤5 at hhi
  change Canon x at cx
  change decode x=advance seed (iter.start.val-1) at vx
  change canon factors at hf
  change ∀ j d s,value factors j d s.val=model seed base (3+k.val) iter.start.val j d s at values
  cases result with
  | done out=>
    obtain ⟨stop,rfl⟩ := FJf_CircleBody.done k iter factors out x run
    have eq : iter.start.val=5 := by omega
    exact ⟨hf,by simpa only [eq] using values⟩
  | cont next=>
    rcases next with ⟨cursor,next,x'⟩
    obtain ⟨heq,hs,more,cx',vx',hf',hv⟩ := FJr_CircleInnerWrite.value k hk iter cursor factors next hf x x' cx run
    refine ⟨?_,?_⟩
    · change cursor.end.val=5 ∧ 1≤cursor.start.val ∧ cursor.start.val≤5 ∧ _
      refine ⟨by rw [heq];exact he,by omega,by omega,cx',?_,hf',?_⟩
      · rw [vx',vx,hs,show iter.start.val+1-1=(iter.start.val-1)+1 by omega,advance]
      · intro j d s
        rw [hv j d s]
        by_cases hj : 3+k.val=j
        · by_cases hd : iter.start.val=d
          · subst d
            rw [if_pos ⟨hj,rfl⟩,vx]
            simp only [model,hj,hs,true_and,if_pos (by omega : 1≤iter.start.val ∧ iter.start.val<iter.start.val+1)]
          · rw [if_neg (by tauto),values j d s]
            have same : d<cursor.start.val ↔ d<iter.start.val := by omega
            simp only [model,hj,same]
        · rw [if_neg (by tauto),values j d s]
          simp only [model,hj,false_and,if_false]
    · simp only [measure,heq,hs];omega

theorem value (k : Usize) (hk : k.val < 2) (factors out : Factors) (hf : canon factors)
    (x : SQ) (cx : Canon x)
    (run : FIn_WeightsExtract.weights_new_loop1_loop0 {start:=1#usize,«end»:=5#usize} factors k x=ok out) :
    Post (decode x) factors (3+k.val) out := by
  exact FIo_LoopInvariant.preserve
    (fun t : State=>FIn_WeightsExtract.weights_new_loop1_loop0.body k t.1 t.2.1 t.2.2)
    (Inv (decode x) factors (3+k.val)) (Post (decode x) factors (3+k.val)) measure
    (fun t h r hr=>by cases r <;> exact step k hk (decode x) factors t h _ hr)
    ({start:=1#usize,«end»:=5#usize},factors,x) out
    ⟨rfl,by change (1:Nat)≤1;omega,by change (1:Nat)≤5;omega,cx,rfl,hf,
      by intro j d s;unfold model;split <;> first | omega | rfl⟩ run

#print axioms step
#print axioms value
end AspisR1.FJr_CircleInnerLoop
end
