import AspisR1ProducerRelease47.MaskColumns51
import R1Z.ProverCommitMle50
import R1Z.ProverCommitMaskWrites51
/-! All 26 source mask-column MLE reads, with every value derived. -/
set_option autoImplicit false
namespace R1Z.ProverCommitMaskColumns51
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisR1.ExtractedCurrentQM31Exact (decode QM31Exact)

def columns (c : Nat → Nat → Old.Q) : Array (Array field.QM31 1024#usize) 26#usize :=
  ⟨List.ofFn (fun i : Fin 26 => ProverCommitQArray48.array 1024#usize (c i.val)),by simp only [List.length_ofFn];rfl⟩

theorem index (c : Nat → Nat → Old.Q) (i : Usize) (hi : i.val<26) :
    Array.index_usize (columns c) i=ok (ProverCommitQArray48.array 1024#usize (c i.val)) := by
  rw [ProverCommitArrayIndex25.array_index_usize_ok _ _ hi]
  simp only [columns,List.getElem_ofFn]

def value (p : Nat → Old.Q) (c : Nat → Nat → Old.Q) (i : Nat) : QM31Exact :=
  AspisR0.RoundNormalization.dot
    (AspisR0.Opening.eqWeight (R0P.SemSource.toR0 (fun j : Fin 10 => decode (p j.val))))
    (fun j : Fin 1024 => decode (c i j.val))

attribute [local irreducible] ProverCommitNativeQ48.source ProverCommitQArray48.array columns value

theorem go (p : Nat → Old.Q) (hp : ∀ i, i<10 → Canonical (p i))
    (c : Nat → Nat → Old.Q) (hc : ∀ i, i<26 → ∀ j, j<1024 → Canonical (c i j))
    (n : Nat) (left : U8) (hl : left.val=n) (hn : n≤26)
    (q : Nat → Old.Q) (hq : ∀ k, k<26 → Canonical (q k)) :
    ∃ z : Nat → Old.Q,
      mask_columns51.go (ProverCommitQArray48.array 10#usize p) (columns c) left
        (ProverCommitQArray48.array 26#usize q)=ok (ProverCommitQArray48.array 26#usize z) ∧
      (∀ k, k<26 → Canonical (z k)) ∧
      ∀ k, k<26 → decode (z k)=if 26-n≤k then value p c k else decode (q k) := by
  induction n generalizing left q with
  | zero =>
    have hz : left=0#u8 := by scalar_tac
    refine ⟨q,?_,hq,?_⟩
    · rw [mask_columns51.go,hz];rfl
    · intro k hk;rw [if_neg (by omega)]
  | succ n ih =>
    have hne : left≠0#u8 := by scalar_tac
    let i := U8.wrapping_sub 26#u8 left
    have hi : i.val=26-(n+1) := by
      dsimp only [i]
      rw [U8.wrapping_sub_val_eq]
      have hs : UScalar.size .U8=256 := by rw [UScalar.size_def];decide
      rw [hs]
      change (26+(256-left.val))%256=26-(n+1)
      rw [hl];omega
    have hib : i.val<26 := by omega
    have hdec : (U8.wrapping_sub left 1#u8).val=n := by
      rw [ProverCommitBasisCounter47.sub_one left (by omega)];omega
    let idx := UScalar.cast .Usize i
    have hidx : idx.val=i.val := by scalar_tac
    obtain ⟨v,hv,hcv,hdv⟩ := ProverCommitMle50.model_result p (c i.val) hp (hc _ hib)
    let next := Function.update q i.val v
    have hcnext : ∀ k, k<26 → Canonical (next k) := by
      intro k hk
      dsimp only [next]
      by_cases h : k=i.val
      · subst k;rw [Function.update_self];exact hcv
      · rw [Function.update_of_ne h];exact hq k hk
    obtain ⟨z,hz,hcz,hdz⟩ := ih _ hdec (by omega) next hcnext
    refine ⟨z,?_,hcz,?_⟩
    · rw [mask_columns51.go]
      simp only [hne,if_false,lift,bind_tc_ok]
      change (do
        let col ← Array.index_usize (columns c) idx
        let cell ← mle50.mle (ProverCommitQArray48.array 10#usize p) col
        let out ← Array.update (ProverCommitQArray48.array 26#usize q) idx cell
        mask_columns51.go (ProverCommitQArray48.array 10#usize p) (columns c) (U8.wrapping_sub left 1#u8) out)=_
      rw [index c idx (by rw [hidx];exact hib)]
      simp only [bind_tc_ok,hidx,hv]
      rw [ProverCommitQArray48.update _ _ idx (by rw [hidx];exact hib),hidx]
      exact hz
    · intro k hk
      rw [hdz k hk]
      by_cases htail : 26-n≤k
      · rw [if_pos htail,if_pos (by omega)]
      · rw [if_neg htail]
        by_cases hstart : k=i.val
        · rw [hstart,if_pos (by omega)]
          dsimp only [next]
          rw [Function.update_self]
          simpa only [value] using hdv
        · have hbefore : ¬26-(n+1)≤k := by omega
          rw [if_neg hbefore]
          exact congrArg decode (Function.update_of_ne hstart _ _)

theorem exact_result (p : Nat → Old.Q) (hp : ∀ i, i<10 → Canonical (p i))
    (c : Nat → Nat → Old.Q) (hc : ∀ i, i<26 → ∀ j, j<1024 → Canonical (c i j)) :
    ∃ z : Nat → Old.Q,
      mask_columns51.eval (ProverCommitQArray48.array 10#usize p) (columns c)=
        ok (ProverCommitQArray48.array 26#usize z) ∧
      (∀ k, k<26 → Canonical (z k)) ∧ ∀ k, k<26 → decode (z k)=value p c k := by
  obtain ⟨z,hz,hcz,hdz⟩ := go p hp c hc 26 26#u8 rfl (by decide)
    (fun _ => zero) (fun _ _ => zero_canonical)
  refine ⟨z,?_,hcz,?_⟩
  · rw [mask_columns51.eval,ProverCommitQArray48.repeat_zero]
    exact hz
  · intro k hk
    simpa only [Nat.sub_self,Nat.zero_le,if_true] using hdz k hk

#print axioms index
#print axioms go
#print axioms exact_result
end R1Z.ProverCommitMaskColumns51
