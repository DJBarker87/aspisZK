import FJf_CircleOuterBody
import FIp_RangeNone
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJr_CircleOuterCuts
open Aeneas Aeneas.Std Result ControlFlow
open FIo_FieldBridge (NE NQ)
open FJf_PointBody (Factors)
open FJf_CircleOuterBody (Z)

theorem head (z : Z) (iter : FIo_RangeNext.Range)
    (weights out : Factors) (more : iter.start.val < iter.end.val)
    (run : FIn_WeightsExtract.weights_new_loop1 iter z weights=ok out) :
    ∃ (cursor : FIo_RangeNext.Range) (next : Factors),
      FIn_WeightsExtract.weights_new_loop1.body z iter weights=ok (.cont (cursor,next)) ∧
      FIn_WeightsExtract.weights_new_loop1 cursor z next=ok out := by
  unfold FIn_WeightsExtract.weights_new_loop1 at run
  rw [loop] at run
  cases hb : FIn_WeightsExtract.weights_new_loop1.body z iter weights with
  | fail e=>simp only [hb] at run;cases run
  | div=>simp only [hb] at run;cases run
  | ok result=>
    simp only [hb] at run
    cases result with
    | done value=>have stop:=(FJf_CircleOuterBody.done z iter weights value hb).1;omega
    | cont next=>exact ⟨next.1,next.2,rfl,run⟩

theorem stopped (z : Z) (iter : FIo_RangeNext.Range)
    (weights out : Factors) (stop : iter.end.val ≤ iter.start.val)
    (run : FIn_WeightsExtract.weights_new_loop1 iter z weights=ok out) :
    out=weights := by
  unfold FIn_WeightsExtract.weights_new_loop1 at run
  rw [loop] at run
  cases hb : FIn_WeightsExtract.weights_new_loop1.body z iter weights with
  | fail e=>simp only [hb] at run;cases run
  | div=>simp only [hb] at run;cases run
  | ok result=>
    simp only [hb] at run
    cases result with
    | done value=>
      cases Result.ok.inj run
      exact (FJf_CircleOuterBody.done z iter weights out hb).2
    | cont next=>
      obtain ⟨side,row,updated,back,digit,x,hn,rest⟩ := FJf_CircleOuterBody.cont z iter next.1 weights next.2 hb
      have more := (FIo_RangeNext.some_next iter next.1 side hn).2.2.2
      omega

#print axioms head
#print axioms stopped
end AspisR1.FJr_CircleOuterCuts
end
