import FJf_PointStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJf_PointLoop
open Aeneas Aeneas.Std Result
open FJf_PointBody (Factors Points)
open FJc_WeightQMBridge (SQ)
open FJf_PointStep

theorem loop (points : Points) (k : Usize) (p : Array SQ 10#usize)
    (hp : Array.index_usize points k=ok p) (hc : FJc_WeightArray.canonical p)
    (base : Factors) (iter : FIo_RangeNext.Range) (factors out : Factors)
    (inv : Inv p k base (iter,factors))
    (run : FIn_WeightsExtract.weights_new_loop0_loop0 iter points factors k=ok out) :
    Post p k base out := by
  exact FIo_LoopInvariant.preserve
    (fun t : State => FIn_WeightsExtract.weights_new_loop0_loop0.body points k t.1 t.2)
    (Inv p k base) (Post p k base) measure
    (fun t h r hr => by cases r <;> exact step points k p hp hc base t h _ hr)
    (iter,factors) out inv run

theorem five (points : Points) (k : Usize) (p : Array SQ 10#usize)
    (hp : Array.index_usize points k=ok p) (hc : FJc_WeightArray.canonical p)
    (factors out : Factors) (hf : FJf_FactorArray.canon factors)
    (run : FIn_WeightsExtract.weights_new_loop0_loop0
      {start:=0#usize,«end»:=5#usize} points factors k=ok out) :
    Post p k factors out := by
  exact loop points k p hp hc factors _ factors out
    ⟨hf,rfl,by change (0:Nat)≤5;decide,by intro j d s;simp only [show (0#usize).val=0 from by decide,
      Nat.not_lt_zero,and_false,if_false]⟩ run
#print axioms loop
#print axioms five
end AspisR1.FJf_PointLoop
end
