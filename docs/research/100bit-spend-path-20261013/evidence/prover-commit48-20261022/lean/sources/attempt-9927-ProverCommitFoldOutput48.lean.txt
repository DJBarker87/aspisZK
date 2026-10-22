import R1Z.ProverCommitFoldValue48
import R1Z.ProverCommitGamma48
/-! Both full primal fold arrays and the complete final-cell image. This
covers the fold kernel, not the weight/round/semantic payload producers. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitFoldOutput48
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitWideOps48 ProverCommitMix48 ProverCommitFoldRange48 ProverCommitFoldValue48

def mathCell (f : Nat → Exact) (a : Exact) (k : Nat) : Exact :=
  f (4*k)+a*f (4*k+1)+a^2*f (4*k+2)+a^3*f (4*k+3)

theorem first_exact (q : Nat → Raw) (hq : ∀ j, j < 1024 → canonical (q j))
    (a : Raw) (ha : canonical a) :
    ∃ ys : Nat → Raw,
      fold_first (sourceArray 1024#usize q) (source a)
        (Array.repeat 256#usize field.wide_exact.WideExact.ZERO) 0#usize 256#u16=ok (sourceArray 256#usize ys) ∧
      (∀ k, k < 256 → canonical (ys k)) ∧
      ∀ k, k < 256 → value (ys k)=mathCell (fun j => value (q j)) (value a) k := by
  obtain ⟨ys,hy,hcy,hval⟩ := range_value 1024#usize 256#usize rfl (by decide)
    q (fun _ => ProverCommitGamma48.zero) hq (fun _ _ => ProverCommitGamma48.zero_canonical)
    a ha 256 0#usize (by scalar_tac)
  refine ⟨ys,?_,hcy,?_⟩
  · rw [first_source 256 _ rfl,ProverCommitGamma48.repeat_zero]
    exact hy
  · intro k hk
    have h := hval k hk
    change value (ys k)=(if 0 ≤ k ∧ k < 0+256 then cellValue q a k else _) at h
    rw [if_pos (by omega)] at h
    exact h

theorem second_exact (q : Nat → Raw) (hq : ∀ j, j < 256 → canonical (q j))
    (a : Raw) (ha : canonical a) :
    ∃ ys : Nat → Raw,
      fold_second (sourceArray 256#usize q) (source a)
        (Array.repeat 64#usize field.wide_exact.WideExact.ZERO) 0#usize 64#u8=ok (sourceArray 64#usize ys) ∧
      (∀ k, k < 64 → canonical (ys k)) ∧
      ∀ k, k < 64 → value (ys k)=mathCell (fun j => value (q j)) (value a) k := by
  obtain ⟨ys,hy,hcy,hval⟩ := range_value 256#usize 64#usize rfl (by decide)
    q (fun _ => ProverCommitGamma48.zero) hq (fun _ _ => ProverCommitGamma48.zero_canonical)
    a ha 64 0#usize (by scalar_tac)
  refine ⟨ys,?_,hcy,?_⟩
  · rw [second_source 64 _ rfl,ProverCommitGamma48.repeat_zero]
    exact hy
  · intro k hk
    have h := hval k hk
    change value (ys k)=(if 0 ≤ k ∧ k < 0+64 then cellValue q a k else _) at h
    rw [if_pos (by omega)] at h
    exact h

def run (q : Array Source 1024#usize) (a b : Source) : Result (Array Source 64#usize) := do
  let mid ← fold_first q a (Array.repeat 256#usize field.wide_exact.WideExact.ZERO) 0#usize 256#u16
  fold_second mid b (Array.repeat 64#usize field.wide_exact.WideExact.ZERO) 0#usize 64#u8

theorem run_image (q : Nat → Raw) (hq : ∀ j, j < 1024 → canonical (q j))
    (a b : Raw) (ha : canonical a) (hb : canonical b) :
    ∃ ys : Nat → Raw,
      run (sourceArray 1024#usize q) (source a) (source b)=ok (sourceArray 64#usize ys) ∧
      (∀ k, k < 64 → canonical (ys k)) ∧
      ∀ k, k < 64 → value (ys k)=
        mathCell (fun j => mathCell (fun s => value (q s)) (value a) j) (value b) k := by
  obtain ⟨mid,hm,hcm,hdm⟩ := first_exact q hq a ha
  obtain ⟨ys,hy,hcy,hval⟩ := second_exact mid hcm b hb
  refine ⟨ys,?_,hcy,?_⟩
  · simp only [run,hm,hy,bind_tc_ok]
  · intro k hk
    rw [hval k hk,mathCell,mathCell,hdm _ (by omega),hdm _ (by omega),
      hdm _ (by omega),hdm _ (by omega)]

theorem fin_bytes (q : Nat → Raw) (hq : ∀ j, j < 1024 → canonical (q j))
    (a b : Raw) (ha : canonical a) (hb : canonical b) :
    ∃ (ys : Nat → Raw) (hys : ∀ k, k < 64 → canonical (ys k)),
      run (sourceArray 1024#usize q) (source a) (source b)=ok (sourceArray 64#usize ys) ∧
      ∀ k : Fin 64, ProverCommitWideBytes48.sourceCell (ys k.val) (hys k.val k.isLt)=
        ProverCommitValueRange47.bytes
          (mathCell (fun j => mathCell (fun s => value (q s)) (value a) j) (value b) k.val) := by
  obtain ⟨ys,hy,hcy,hval⟩ := run_image q hq a b ha hb
  refine ⟨ys,hcy,hy,?_⟩
  intro k
  rw [ProverCommitWideBytes48.source_image,hval k.val k.isLt]

#print axioms first_exact
#print axioms second_exact
#print axioms run_image
#print axioms fin_bytes
end R1Z.ProverCommitFoldOutput48
