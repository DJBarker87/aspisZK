import JHv_Leaves
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHv_LeafObservations
open Aeneas Aeneas.Std Result
open _root_.AdapterRw

theorem policy : PoolS2_PolicySource.pool_v1.format.validate_verifier_policy_v1
    JHg_AccountValues.master.verifier_policy=ok (.Ok ()) := by
  apply PoolS2_PolicyExact.ready
  refine ⟨?_,?_,?_,?_,?_⟩
  · change (3#u8 &&& ~~~3#u8)=0#u8; exact Eq.refl _
  · intro h
    have bad := congrArg (fun a : solana_pubkey.Pubkey => a.val.head?) h
    change some (68#u8 : U8)=some 0#u8 at bad
    have impossible := Option.some.inj bad
    scalar_tac
  · intro h
    have bad := congrArg (fun a : solana_pubkey.Pubkey => a.val.head?) h
    change some (7#u8 : U8)=some 0#u8 at bad
    have impossible := Option.some.inj bad
    scalar_tac
  · intro _; change (3#u8 &&& 1#u8 != 0#u8)=true; exact Eq.refl _
  · constructor
    · intro _; exact Eq.refl _
    · intro _; change (3#u8 &&& 1#u8 != 0#u8)=true; exact Eq.refl _
#print axioms policy

theorem immutable : NBX_SlotValues.op28 JHj_RegistryValue.registry=ok true := by
  change ok (2#u8 &&& 2#u8 != 0#u8)=ok true
  exact Eq.refl _
#print axioms immutable

theorem unrevoked : NBX_SlotValues.op27 JHj_RegistryValue.registry=ok false := by
  change ok (2#u8 &&& 1#u8 != 0#u8)=ok false
  exact Eq.refl _
#print axioms unrevoked

theorem active (slot : U64) : NBX_SlotValues.op29 JHj_RegistryValue.entry slot=ok true := by
  change ok (true && decide (0#u64 ≤ slot) &&
    (decide (18446744073709551615#u64=18446744073709551615#u64) ||
      decide (slot < 18446744073709551615#u64)))=ok true
  have lower : 0#u64 ≤ slot := by scalar_tac
  simp only [lower,decide_true,Bool.true_and,Bool.true_or]
#print axioms active
end AspisR1.JHv_LeafObservations
end
