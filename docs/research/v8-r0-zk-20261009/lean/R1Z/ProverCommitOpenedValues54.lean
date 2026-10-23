import R1Z.ProverCommitOpenedColumn54
import R1Z.ProverCommitEncoderInitial54
/-! Complete retained 29-column opened-value caller with encoder provenance. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitOpenedValues54
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitWideOps48 ProverCommitMix48 ProverCommitOpenedColumn54

def coefficients (c : Nat → Nat → Raw) : Array (Array Source 1024#usize) 29#usize :=
  ProverCommitArray49.array 29#usize (fun l => sourceArray 1024#usize (c l))

def symbol (c : Nat → Nat → Raw) (u : Fin 262144) (s : Fin 4) (l : Nat) : Exact :=
  AspisWide.InitialEncoder.exactInitialEncoder (fun i => value (c l i.val))
    (AspisV5ComponentCConcreteFoldLinearity.childIndex u s)

attribute [local irreducible] coefficients matrix sourceArray source value symbol

theorem opened (c : Nat → Nat → Raw) (hc : ∀ l, l<29 → ∀ i, i<1024 → canonical (c l i))
    (j : Usize) (u : Fin 262144) (hj : j.val=u.val) (n : Nat) (l : Usize) (left : U8)
    (hl : left.val=n) (bound : l.val+n≤29)
    (xs : Nat → Nat → Raw) (hxs : ∀ s, s<4 → ∀ k, k<29 → canonical (xs s k)) :
    ∃ out : Nat → Nat → Raw,
      leaves54.opened (coefficients c) j l left (matrix xs)=ok (matrix out) ∧
      (∀ s, s<4 → ∀ k, k<29 → canonical (out s k)) ∧
      ∀ (s : Fin 4) k, k<29 → value (out s.val k)=
        if l.val ≤ k ∧ k<l.val+n then symbol c u s k else value (xs s.val k) := by
  induction n generalizing l left xs with
  | zero =>
    have hz : left=0#u8 := by scalar_tac
    refine ⟨xs,?_,hxs,?_⟩
    · rw [leaves54.opened,hz];rfl
    · intro s k hk;rw [if_neg (by omega)]
  | succ n ih =>
    have hne : left≠0#u8 := by scalar_tac
    have hlb : l.val<29 := by omega
    have hdec : (U8.wrapping_sub left 1#u8).val=n := by
      rw [ProverCommitBasisCounter47.sub_one left (by omega)];omega
    have hinc : (Usize.wrapping_add l 1#usize).val=l.val+1 :=
      ProverCommitPairCounter47.next_val l (by omega)
    obtain ⟨h,hh,hch,hdh⟩ := ProverCommitEncoderInitial54.exact_result (c l.val) (hc _ hlb) j u hj
    obtain ⟨next,hnext,hdnext⟩ := column h l 0#usize hlb 4 4#u8 rfl (by decide) xs
    have hnextraw : ∀ s k, s<4 → k<29 → next s k=if k=l.val then h s else xs s k := by
      intro s k hs hk
      simpa only [show (0#usize).val=0 from rfl,Nat.zero_add,Nat.zero_le,hs,true_and] using hdnext s k hs hk
    have hcnext : ∀ s, s<4 → ∀ k, k<29 → canonical (next s k) := by
      intro s hs k hk
      rw [hnextraw s k hs hk]
      split
      · exact hch s hs
      · exact hxs s hs k hk
    obtain ⟨out,hout,hcout,hdout⟩ := ih (Usize.wrapping_add l 1#usize) _ hdec
      (by rw [hinc];omega) next hcnext
    refine ⟨out,?_,hcout,?_⟩
    · rw [leaves54.opened]
      simp only [hne,if_false]
      have hindex : Array.index_usize (coefficients c) l=ok (sourceArray 1024#usize (c l.val)) := by
        unfold coefficients
        exact ProverCommitArray49.index 29#usize _ l hlb
      rw [hindex];simp only [bind_tc_ok,hh,hnext,lift]
      exact hout
    · intro s k hk
      rw [hdout s k hk,hinc]
      by_cases he : k=l.val
      · subst k
        rw [if_neg (by omega),if_pos (by omega),hnextraw s.val l.val s.isLt hlb,if_pos rfl]
        simpa only [symbol] using hdh s
      · by_cases ht : l.val+1 ≤ k ∧ k<l.val+1+n
        · rw [if_pos ht,if_pos (by omega)]
        · rw [if_neg ht,if_neg (by omega),hnextraw s.val k s.isLt hk,if_neg he]

theorem exact_result (c : Nat → Nat → Raw)
    (hc : ∀ l, l<29 → ∀ i, i<1024 → canonical (c l i))
    (j : Usize) (u : Fin 262144) (hj : j.val=u.val) :
    ∃ out : Nat → Nat → Raw, leaves54.opened_values (coefficients c) j=ok (matrix out) ∧
      (∀ s, s<4 → ∀ l, l<29 → canonical (out s l)) ∧
      ∀ (s : Fin 4) (l : Fin 29), value (out s.val l.val)=symbol c u s l.val := by
  let zero : Raw := (ProverCommitSubfieldOps47.zero,ProverCommitSubfieldOps47.zero)
  have hczero : canonical zero := ⟨ProverCommitSubfieldOps47.zero_canonical,ProverCommitSubfieldOps47.zero_canonical⟩
  obtain ⟨out,hout,hcout,hdout⟩ := opened c hc j u hj 29 0#usize 29#u8 rfl (by decide)
    (fun _ _ => zero) (fun _ _ _ _ => hczero)
  refine ⟨out,?_,hcout,?_⟩
  · rw [leaves54.opened_values]
    have hz : Array.repeat 4#usize (Array.repeat 29#usize field.wide_exact.WideExact.ZERO)=matrix (fun _ _ => zero) := by
      unfold matrix sourceArray ProverCommitArray49.array
      have hz0 : field.wide_exact.WideExact.ZERO=source zero := by
        simp only [field.wide_exact.WideExact.ZERO,field.QM31.ZERO,source,pack,
          ProverCommitRelease47.convE,ProverCommitRelease47.convQ,ProverCommitRelease47.convC,
          ProverCommitPrimitive47.fromQ,ProverCommitPrimitive47.fromC,zero,ProverCommitSubfieldOps47.zero]
      rw [hz0]
      simp only [Array.repeat,List.ofFn_const]
    rw [hz,hout]
  · intro s l
    simpa only [show (0#usize).val=0 from rfl,Nat.zero_add,Nat.zero_le,l.isLt,and_self,if_true] using hdout s l.val l.isLt

#print axioms opened
#print axioms exact_result
end R1Z.ProverCommitOpenedValues54
