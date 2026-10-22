import R1Z.ProverCommitCounterList48
import R1Z.ProverCommitRoundLoop48
import R1Z.ProverCommitGamma48
/-! Complete unscaled round accumulation for the native nested d/s/t order. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitRoundOutput48
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitWideOps48 ProverCommitMix48 ProverCommitRoundLoop48 ProverCommitCounterList48

def indices (n : Nat) : List Triple :=
  (counters n 0#usize).flatMap (fun d => (counters 4 0#usize).flatMap
    (fun s => (counters 4 0#usize).map (fun t => (d,s,t))))

theorem indices_legal (n : Nat) (hn : n ≤ 256) : ∀ u ∈ indices n, legal u := by
  intro u hu
  simp only [indices,List.mem_flatMap,List.mem_map] at hu
  obtain ⟨d,hd,s,hs,t,ht,rfl⟩ := hu
  have h0 : (0#usize).val=0 := rfl
  have hdb := bounds n 0#usize (by rw [h0];omega) d hd
  have hsb := bounds 4 0#usize (by rw [h0];omega) s hs
  have htb := bounds 4 0#usize (by rw [h0];omega) t ht
  simp only [h0,Nat.zero_add] at hdb hsb htb
  change d.val < 256 ∧ s.val < 4 ∧ t.val < 4
  exact ⟨by omega,hsb.2,htb.2⟩

def run (n : Nat) (q w : Array Source 1024#usize) : Result (Array Source 7#usize) :=
  loop q w (indices n) (Array.repeat 7#usize field.wide_exact.WideExact.ZERO)

theorem accumulation (n : Nat) (hn : n ≤ 256) (q w : Nat → Raw)
    (hq : ∀ k, k < 1024 → canonical (q k)) (hw : ∀ k, k < 1024 → canonical (w k)) :
    ∃ ys : Nat → Raw, run n (sourceArray 1024#usize q) (sourceArray 1024#usize w)=
      ok (sourceArray 7#usize ys) ∧ (∀ k, k < 7 → canonical (ys k)) ∧
      ∀ k, k < 7 → value (ys k)=terms q w (indices n) k := by
  obtain ⟨ys,hy,hcy,hdy⟩ := loop_value q w hq hw (indices n) (indices_legal n hn)
    (fun _ => ProverCommitGamma48.zero) (fun _ _ => ProverCommitGamma48.zero_canonical)
  refine ⟨ys,?_,hcy,?_⟩
  · simp only [run,ProverCommitGamma48.repeat_zero,hy]
  · intro k hk
    simpa only [ProverCommitGamma48.zero_value,zero_add] using hdy k hk

#print axioms indices_legal
#print axioms accumulation
end R1Z.ProverCommitRoundOutput48
