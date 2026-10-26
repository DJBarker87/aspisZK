import RPx_OuterDecoded
set_option autoImplicit false
noncomputable section
namespace AspisR1.RPx_OuterStage2
open Aeneas Aeneas.Std Result S2W_Trace S2W_Outer RPx_OuterCredit

theorem returned_credit {A B : Type} (a : A) (k : A → Code B) (n : Nat)
    (h : Credit (k a) n) : Credit ((monadLift (ok a) : Code A) >>= k) n := h

theorem call_credit {A : Type} (op : Call A) (n : Nat) (h : charge op≤n) :
    Credit (perform op) n := ⟨h,fun _=>trivial⟩

attribute [local irreducible] Credit S2W_Outer.mapError

theorem stage2 (sdk : AdapterRw.Ops)
    (program : AdapterRw.solana_pubkey.Pubkey) (accounts : Slice AdapterRw.r1_pool_adapter.owned.OwnedAccount)
    (data : Slice U8) (slot : S2W_ExtractionBoundary.Slot) :
    Credit (stage2_owned sdk traceEffects program accounts data slot) 903 := by
  unfold stage2_owned
  simp only [AdapterRw.observer]
  repeat' first
    | (solve | exact pure_credit _ _)
    | (solve | exact lift_credit _ _)
    | (apply returned_credit)
    | (apply lift_bind_credit;intro x)
    | (apply call_bind_credit; (first | (solve | simp only [charge];omega) | intro x))
    | (apply RPx_OuterDecoded.map_bind;intro x)
    | (solve | apply call_credit; simp only [charge];omega)
    | intro x
    | (fail_if_no_progress dsimp only)
    | split

#print axioms returned_credit
#print axioms call_credit
#print axioms stage2
end AspisR1.RPx_OuterStage2
end
