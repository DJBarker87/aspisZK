import R1Z.PV_RDEA_ClonePrefix
open Aeneas Aeneas.Std
namespace R1Z.PV_RDEA_CloneSuccessWord
open PV_RDB1_V183_ReserveWorld PV_RDEA_CapacityEndpoint PV_RDEA_PrefixWords

theorem constructor_word_success {S F : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (width : shape.width=1) (address n : Nat) (w : World S F)
    (success : (PV_RDB1_V181.deployed step 18446744073709551615
      9223372036854775807 shape address n w).returned=.ok ()) :
    requestSizes n=cloneWord n := by
  have bounds := PV_RDEA_ClonePrefix.success_bounds step _ _ shape address n w success
  have hw : ¬n>18446744073709551615 := by omega
  have hb : ¬n>9223372036854775807 := by rw [width] at bounds; simp only [Nat.mul_one] at bounds; omega
  simp only [requestSizes,cloneWord,hw,hb,ite_false]

theorem clone_word_success {S F : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (width : shape.width=1) (address : Nat)
    (base : List U8) (w : World S F) (b : Buffer U8)
    (success : (PV_RDEA_CloneExecution.clone step shape address base w).1=.ok b) :
    sizes (PV_RDEA_CloneExecution.clone step shape address base w).2.history =
      sizes w.history++cloneWord base.length := by
  have hr : (PV_RDB1_V181.deployed step 18446744073709551615
      9223372036854775807 shape address base.length w).returned=.ok () := by
    unfold PV_RDEA_CloneExecution.clone at success
    dsimp only at success
    split at success <;> rename_i h
    · cases success
    · exact h
  rw [PV_RDEA_CloneExecution.clone_sizes step shape width,
    constructor_word_success step shape width address base.length w hr]

#print axioms constructor_word_success
#print axioms clone_word_success
end R1Z.PV_RDEA_CloneSuccessWord
