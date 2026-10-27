import R1Z.PV_L2_F3CountedArrays
import R1Z.PV_L2_F3Law

/-! Conditional count/value law on the ACTUAL raw OracleAnswer block carrier
used by FinalR1PBin.wordsE and the owned decoder. No independently sampled
successful mask array replaces that carrier. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_L2_F3Blocks
open R0Z R0Z.FsStatement R1Z.CommitReadsR1 R1Z.FinalR1PBin
  R1Z.ProverCommitWordCarrier R1Z.PV_L2_F3CountedArrays R1Z.PV_L2_F3Law
attribute [local instance] Classical.propDecidable
attribute [local irreducible] sourceBase

theorem precompose_card {I J : Type} [Fintype I] [Fintype J] (e : I ≃ J) (pred : J → Prop) :
    (Finset.univ.filter (fun i => pred (e i))).card = (Finset.univ.filter pred).card := by
  apply Finset.card_bij (fun i _ => e i)
  · intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2⟩
  · intro i hi j hj same;exact e.injective same
  · intro j hj
    refine ⟨e.symm j,?_,e.apply_symm_apply j⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by
      simpa only [e.apply_symm_apply] using (Finset.mem_filter.mp hj).2⟩

variable {K : Type} [Field K] [Algebra (ZMod AspisCircleGroupOrder.P) K]
local notation "F" => sourceBase (K := K)

def blocks (E L : Nat) (input : Fin E → OracleAnswer) :
    Option ((Fin L → F) × (Fin L → Nat)) :=
  arrays (accepted (K := K)) (E*8) L 16 (wordsE E input)

theorem word_arrays_fibres (n L r : Nat) (a b : Fin L → F) (history : Fin L → Nat) :
    (Finset.univ.filter (fun ws : Fin n → R1Z.CommitReadsR1.Word => arrays (accepted (K := K)) n L r ws = some (a,history))).card =
      (Finset.univ.filter (fun ws : Fin n → R1Z.CommitReadsR1.Word => arrays (accepted (K := K)) n L r ws = some (b,history))).card := by
  let eqv := PV_L2_F3CountedArrays.split F L
  have heq (out : (Fin L → F) × (Fin L → Nat)) :
      (Finset.univ.filter (fun ws : Fin n → R1Z.CommitReadsR1.Word =>
        arrays (accepted (K := K)) n L r ws = some out)) =
      Finset.univ.filter (fun ws : Fin n → R1Z.CommitReadsR1.Word =>
        PV_L2_F3CountedFibres.counted (accepted (K := K)) n L r ws = some (eqv.symm out)) := by
    ext ws
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,arrays]
    exact ProverCommitSourceDecoder.map_equiv_some eqv _ out
  rw [heq,heq]
  have same : PV_L2_F3CountedFibres.counts L (eqv.symm (a,history)) =
      PV_L2_F3CountedFibres.counts L (eqv.symm (b,history)) := by
    apply (ProverCommitSequentialFibres.valuesEquiv Nat L).injective
    rw [← PV_L2_F3CountedArrays.split_counts,← PV_L2_F3CountedArrays.split_counts]
    change (eqv (eqv.symm (a,history))).2 = (eqv (eqv.symm (b,history))).2
    simp only [Equiv.apply_symm_apply]
  convert PV_L2_F3CountedErasure.actual_word_conditioned (K := K) n L r
    (eqv.symm (a,history)) (eqv.symm (b,history)) same using 1 <;>
      apply congrArg Finset.card <;> ext ws <;>
        simp only [Finset.mem_filter,Finset.mem_univ,true_and]

theorem block_fibres (E L : Nat) (a b : Fin L → F) (history : Fin L → Nat) :
    (Finset.univ.filter (fun input => blocks (K := K) E L input = some (a,history))).card =
      (Finset.univ.filter (fun input => blocks (K := K) E L input = some (b,history))).card := by
  unfold blocks
  have ha := precompose_card (wordsE E) (fun ws => arrays (accepted (K := K)) (E*8) L 16 ws = some (a,history))
  have hb := precompose_card (wordsE E) (fun ws => arrays (accepted (K := K)) (E*8) L 16 ws = some (b,history))
  calc
    _ = (Finset.univ.filter (fun ws : Fin (E*8) → R1Z.CommitReadsR1.Word =>
      arrays (accepted (K := K)) (E*8) L 16 ws = some (a,history))).card := by
        convert ha using 1 <;> apply congrArg Finset.card <;> ext ws <;>
          simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    _ = (Finset.univ.filter (fun ws : Fin (E*8) → R1Z.CommitReadsR1.Word =>
      arrays (accepted (K := K)) (E*8) L 16 ws = some (b,history))).card :=
        word_arrays_fibres (E*8) L 16 a b history
    _ = _ := by
      convert hb.symm using 1 <;> apply congrArg Finset.card <;> ext ws <;>
        simp only [Finset.mem_filter,Finset.mem_univ,true_and]

theorem blocks_joint_law (E L : Nat) (e : (Fin L → Nat) → (Fin L → F) ≃ (Fin L → F)) :
    EqualLaws (fun input => (blocks (K := K) E L input).map (fun p => (e p.2 p.1,p.2)))
      (blocks (K := K) E L) := by
  apply conditional_relabel
  intro history a b
  convert block_fibres (K := K) E L a b history using 1 <;>
    apply congrArg Finset.card <;> ext ws <;>
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]

#print axioms precompose_card
#print axioms word_arrays_fibres
#print axioms block_fibres
#print axioms blocks_joint_law
end R1Z.PV_L2_F3Blocks
