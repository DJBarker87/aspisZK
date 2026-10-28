import R1Z.PV_RunJoin_WeightPowerBits46
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightPower46
open Aeneas Aeneas.Std Result ControlFlow PV_RunJoin_WeightCarrier46
open PV_RunJoin_WeightMap46 (mapResult)

theorem loop (n : Nat) (e64 : U64) (e8 : U8) (he64 : e64.val=n) (he8 : e8.val=n)
    (base acc : Q) :
    AspisR1ProducerRelease47.kernels.power (toQ base) e8 (toQ acc)=
      mapResult toQ (PV_B2_251c1.aspis_core.field.QM31.pow_loop e64 base acc) := by
  induction n using Nat.strong_induction_on generalizing e64 e8 base acc with
  | h n ih =>
    by_cases hn : n=0
    · have h64 : e64=0#u64 := by scalar_tac
      have h8 : e8=0#u8 := by scalar_tac
      subst e64
      subst e8
      rw [AspisR1ProducerRelease47.kernels.power]
      unfold PV_B2_251c1.aspis_core.field.QM31.pow_loop
      rw [Aeneas.Std.loop.eq_def]
      rfl
    · have hgt : e64>0#u64 := by scalar_tac
      have hz : e8≠0#u8 := by scalar_tac
      have hs64 : (U64.wrapping_shr e64 1#u32).val=n/2 := by
        rw [PV_RunJoin_WeightPowerBits46.shift64,he64]
      have hs8 : (U8.wrapping_shr e8 1#u32).val=n/2 := by
        rw [ProverCommitPowerStep49.shift,he8]
      obtain ⟨a1,ha1⟩ : ∃ a1,
          (if n%2≠0 then PV_B2_251c1.aspis_core.field.QM31.mul acc base else ok acc)=ok a1 := by
        by_cases hp : n%2≠0
        · refine ⟨PV_B2_C_251FieldValue.aspis_core.field.QM31.mul acc base,?_⟩
          rw [if_pos hp,PV_B2_C_251FieldTotal.QM31_mul]
        · exact ⟨acc,by rw [if_neg hp]⟩
      obtain ⟨b1,hb1⟩ := PV_B2_D_PowTotal.square base
      have hm : (if ((e8 &&& 1#u8) != 0#u8) then
          AspisR1ProducerRelease47.field.QM31.mul (toQ acc) (toQ base)
          else ok (toQ acc))=ok (toQ a1) := by
        simp only [ProverCommitPowerStep49.condition,he8,decide_eq_true_eq]
        by_cases hp : n%2≠0
        · rw [if_pos hp] at ha1 ⊢
          rw [PV_RunJoin_WeightQuartic46.mul,ha1]
          rfl
        · rw [if_neg hp] at ha1 ⊢
          cases Result.ok.inj ha1
          rfl
      have hs : AspisR1ProducerRelease47.field.QM31.square (toQ base)=ok (toQ b1) := by
        rw [PV_RunJoin_WeightSquare46.complete,hb1]
        rfl
      have hbody : PV_B2_251c1.aspis_core.field.QM31.pow_loop.body e64 base acc=
          ok (cont (U64.wrapping_shr e64 1#u32,b1,a1)) := by
        simp only [PV_B2_251c1.aspis_core.field.QM31.pow_loop.body,hgt,if_true,
          PV_RunJoin_WeightPowerBits46.condition64,he64,lift,bind_tc_ok,ha1,hb1]
      have hr := ih (n/2) (Nat.div_lt_self (by omega) (by decide)) _ _ hs64 hs8 b1 a1
      rw [AspisR1ProducerRelease47.kernels.power]
      simp only [hz,if_false,lift,bind_tc_ok,hm,hs]
      unfold PV_B2_251c1.aspis_core.field.QM31.pow_loop
      rw [Aeneas.Std.loop.eq_def]
      simp only [hbody,bind_tc_ok]
      exact hr

theorem complete (base : Q) (e64 : U64) (e8 : U8) (he : e64.val=e8.val) :
    AspisR1ProducerRelease47.kernels.power (toQ base) e8 AspisR1ProducerRelease47.field.QM31.ONE=
      mapResult toQ (PV_B2_251c1.aspis_core.field.QM31.pow base e64) := by
  rw [PV_RunJoin_WeightQuartic46.one]
  exact loop e8.val e64 e8 he rfl base _
#print axioms loop
#print axioms complete
end R1Z.PV_RunJoin_WeightPower46
