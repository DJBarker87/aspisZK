import R1Z.PV_L2_F3Blocks

/-! The two actual source streams jointly retain per-scalar draw counts.
None preserves the original decoder's failure, not a replacement mask draw. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_L2_F3Pair
open R0Z R0Z.FsStatement R1Z.PV_L2_F3Blocks R1Z.PV_L2_F3CountedArrays
  R1Z.ProverCommitWordCarrier R1Z.FinalR1PBin R1Z.ProverCommitSequentialFibres
attribute [local instance] Classical.propDecidable
attribute [local irreducible] sourceBase
variable {K : Type} [Field K] [Algebra (ZMod AspisCircleGroupOrder.P) K]
local notation "F" => sourceBase (K := K)

def pair (E₁ E₂ L₁ L₂ : Nat) (input : (Fin E₁ → OracleAnswer) × (Fin E₂ → OracleAnswer)) :
    Option (((Fin L₁ → F) × (Fin L₂ → F)) × ((Fin L₁ → Nat) × (Fin L₂ → Nat))) := do
  let a ← blocks E₁ L₁ input.1
  let b ← blocks E₂ L₂ input.2
  pure ((a.1,b.1),(a.2,b.2))

theorem fibre_product (E₁ E₂ L₁ L₂ : Nat)
    (a : Fin L₁ → F) (b : Fin L₂ → F) (ha : Fin L₁ → Nat) (hb : Fin L₂ → Nat) :
    (Finset.univ.filter (fun input => pair E₁ E₂ L₁ L₂ input = some ((a,b),(ha,hb)))).card =
      (Finset.univ.filter (fun x => blocks E₁ L₁ x = some (a,ha))).card *
      (Finset.univ.filter (fun y => blocks E₂ L₂ y = some (b,hb))).card := by
  have hs : (Finset.univ.filter (fun input => pair E₁ E₂ L₁ L₂ input = some ((a,b),(ha,hb)))) =
      (Finset.univ.filter (fun x => blocks E₁ L₁ x = some (a,ha))) ×ˢ
        (Finset.univ.filter (fun y => blocks E₂ L₂ y = some (b,hb))) := by
    ext input
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_product]
    cases h1 : blocks (K := K) E₁ L₁ input.1 <;>
      cases h2 : blocks (K := K) E₂ L₂ input.2 <;> simp [pair,h1,h2,Prod.ext_iff,and_left_comm,and_assoc,and_comm]
  rw [hs,Finset.card_product]

theorem pair_fibres (E₁ E₂ L₁ L₂ : Nat)
    (a a' : Fin L₁ → F) (b b' : Fin L₂ → F)
    (history : (Fin L₁ → Nat) × (Fin L₂ → Nat)) :
    (Finset.univ.filter (fun input => pair E₁ E₂ L₁ L₂ input = some ((a,b),history))).card =
      (Finset.univ.filter (fun input => pair E₁ E₂ L₁ L₂ input = some ((a',b'),history))).card := by
  rcases history with ⟨ha,hb⟩
  rw [fibre_product,fibre_product]
  exact congrArg₂ Nat.mul (block_fibres E₁ L₁ a a' ha) (block_fibres E₂ L₂ b b' hb)

theorem pair_erases (E₁ E₂ L₁ L₂ : Nat)
    (input : (Fin E₁ → OracleAnswer) × (Fin E₂ → OracleAnswer)) :
    (pair (K := K) E₁ E₂ L₁ L₂ input).map Prod.fst =
      pairDecode (accepted (K := K)) (E₁*8) (E₂*8) L₁ L₂
        (wordsE E₁ input.1,wordsE E₂ input.2) := by
  unfold pair pairDecode
  rw [← arrays_erases (accepted (K := K)) (E₁*8) L₁ 16 (wordsE E₁ input.1),
    ← arrays_erases (accepted (K := K)) (E₂*8) L₂ 16 (wordsE E₂ input.2)]
  change _ = (do
    let a ← (blocks (K := K) E₁ L₁ input.1).map Prod.fst
    let b ← (blocks (K := K) E₂ L₂ input.2).map Prod.fst
    pure (a,b))
  cases h1 : blocks (K := K) E₁ L₁ input.1 <;>
    cases h2 : blocks (K := K) E₂ L₂ input.2 <;> rfl

theorem pair_joint_law (E₁ E₂ L₁ L₂ : Nat)
    (e : ((Fin L₁ → Nat) × (Fin L₂ → Nat)) →
      ((Fin L₁ → F) × (Fin L₂ → F)) ≃ ((Fin L₁ → F) × (Fin L₂ → F))) :
    EqualLaws (fun input => (pair (K := K) E₁ E₂ L₁ L₂ input).map (fun p => (e p.2 p.1,p.2)))
      (pair (K := K) E₁ E₂ L₁ L₂) := by
  apply PV_L2_F3Law.conditional_relabel
  intro history a b
  rcases a with ⟨a1,a2⟩
  rcases b with ⟨b1,b2⟩
  convert pair_fibres E₁ E₂ L₁ L₂ a1 b1 a2 b2 history using 1 <;>
    apply congrArg Finset.card <;> ext input <;>
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]

#print axioms fibre_product
#print axioms pair_fibres
#print axioms pair_erases
#print axioms pair_joint_law
end R1Z.PV_L2_F3Pair
