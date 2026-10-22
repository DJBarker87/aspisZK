import R1Z.ProverCommitRoundShape49
import R1Z.ProverCommitDualOutput49
import R1Z.ProverCommitPrimalModel49
/-! Opening kernel caller: first round, both first folds, second round and
final primal fold, from arbitrary canonical batch and weight arrays. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitOpeningKernel49
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitWideOps48 ProverCommitMix48

def run (q w : Array Source 1024#usize) (a b : Source) :
    Result (List Source × Array Source 256#usize × List Source × Array Source 64#usize) := do
  let c0 ← ProverCommitRoundScaled48.run 256 q w
  let q1 ← fold_first q a (Array.repeat 256#usize field.wide_exact.WideExact.ZERO) 0#usize 256#u16
  let w1 ← dual.all w a
  let c1 ← ProverCommitRoundShape49.run q1 w1
  let fin ← fold_second q1 b (Array.repeat 64#usize field.wide_exact.WideExact.ZERO) 0#usize 64#u8
  ok (c0,q1,c1,fin)

attribute [local irreducible] value sourceArray source

theorem exact_result (q w : Nat → Raw)
    (hq : ∀ i, i<1024 → canonical (q i)) (hw : ∀ i, i<1024 → canonical (w i))
    (a b : Raw) (ha : canonical a) (hb : canonical b) :
    ∃ c0 q1 w1 c1 fin : Nat → Raw,
      run (sourceArray 1024#usize q) (sourceArray 1024#usize w) (source a) (source b)=
        ok (List.ofFn (fun k : Fin 7 => source (c0 k.val)),sourceArray 256#usize q1,
          List.ofFn (fun k : Fin 7 => source (c1 k.val)),sourceArray 64#usize fin) ∧
      (∀ k, k<7 → canonical (c0 k) ∧ canonical (c1 k)) ∧
      (∀ i, i<256 → canonical (q1 i) ∧ canonical (w1 i)) ∧
      (∀ i, i<64 → canonical (fin i)) ∧
      (∀ i : Fin 256, value (q1 i.val)=AspisR1.RoundPairing.primalFold (value a) (fun j : Fin 1024 => value (q j.val)) i) ∧
      (∀ i : Fin 256, value (w1 i.val)=AspisR1.RoundPairing.dualFold (value a) (fun j : Fin 1024 => value (w j.val)) i) ∧
      (∀ k : Fin 7, value (c0 k.val)=(AspisR1.RoundPairing.roundPolynomial (n:=256)
        (fun j => value (q j.val)) (fun j => value (w j.val))).coeff k.val) ∧
      (∀ k : Fin 7, value (c1 k.val)=(AspisR1.RoundPairing.roundPolynomial (n:=64)
        (AspisR1.RoundPairing.primalFold (value a) (fun j : Fin 1024 => value (q j.val)))
        (AspisR1.RoundPairing.dualFold (value a) (fun j : Fin 1024 => value (w j.val)))).coeff k.val) ∧
      (∀ i : Fin 64, value (fin i.val)=AspisR1.RoundPairing.primalFold (value b)
        (AspisR1.RoundPairing.primalFold (value a) (fun j : Fin 1024 => value (q j.val))) i) := by
  obtain ⟨c0,hc0,hcc0,hdc0⟩ := ProverCommitRoundModel49.coefficients 256 (by decide) q w hq hw
  obtain ⟨q1,hq1,hcq1,hdq1⟩ := ProverCommitFoldOutput48.first_exact q hq a ha
  obtain ⟨w1,hw1,hcw1,hdw1⟩ := ProverCommitDualOutput49.all w hw a ha
  obtain ⟨c1,hc1,hcc1,hdc1⟩ := ProverCommitRoundShape49.second_coefficients q1 w1 hcq1 hcw1
  obtain ⟨fin,hfin,hcfin,hdfin⟩ := ProverCommitFoldOutput48.second_exact q1 hcq1 b hb
  have hqmodel : (fun i : Fin 256 => value (q1 i.val))=
      AspisR1.RoundPairing.primalFold (value a) (fun j : Fin 1024 => value (q j.val)) := by
    funext i
    rw [hdq1 i.val i.isLt]
    exact ProverCommitPrimalModel49.cell_model 256 q (value a) i
  have hwmodel : (fun i : Fin 256 => value (w1 i.val))=
      AspisR1.RoundPairing.dualFold (value a) (fun j : Fin 1024 => value (w j.val)) := funext hdw1
  refine ⟨c0,q1,w1,c1,fin,?_,fun k hk => ⟨hcc0 k hk,hcc1 k hk⟩,
    fun i hi => ⟨hcq1 i hi,hcw1 i hi⟩,hcfin,congrFun hqmodel,hdw1,hdc0,?_,?_⟩
  · simp only [run,hc0,hq1,hw1,hc1,hfin,bind_tc_ok]
  · intro k
    simpa only [hqmodel,hwmodel] using hdc1 k
  · intro i
    rw [hdfin i.val i.isLt,ProverCommitPrimalModel49.cell_model 64 q1 (value b) i,hqmodel]

#print axioms exact_result
end R1Z.ProverCommitOpeningKernel49
