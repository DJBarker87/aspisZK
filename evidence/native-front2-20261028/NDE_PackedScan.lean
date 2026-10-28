import RPv_FJe_PackedBound
import RPu_FIq_Native05
import RPv_JFy_Specs
set_option autoImplicit false
noncomputable section
namespace AspisR1.NDE_PackedScan
open Aeneas Aeneas.Std Result WP FIq_Native
abbrev Table := Array (Array U64 4#usize) 4#usize
theorem inner (n : Nat) (table : Table) (flag : Bool) (row limb : Usize)
    (hr : row.val<4) (hn : limb.val+n=4) :
    ∃ out,state_only_poseidon.external_local_packed_raw_loop0_loop0 table flag row limb=ok out := by
  induction n generalizing limb flag with
  | zero =>
    have h : ¬limb<4#usize := by scalar_tac
    exact ⟨flag,by rw [state_only_poseidon.external_local_packed_raw_loop0_loop0.eq_def,if_neg h]⟩
  | succ n ih =>
    have h : limb<4#usize := by scalar_tac
    have spec : (do
      let a ← Array.index_usize table row
      let i ← Array.index_usize a limb
      let b ← state_only_poseidon.EXTERNAL_LOCAL_LIMB_MODULUS_BOUND
      let next ← limb+1#usize
      ok (flag && (i<b),next)) ⦃ p=>p.2.val=limb.val+1 ⦄ := by
      obtain ⟨b,rb,_,_⟩ := FJe_PackedBound.value
      rw [show state_only_poseidon.EXTERNAL_LOCAL_LIMB_MODULUS_BOUND=ok b from rb]
      step* <;> scalar_tac
    obtain ⟨⟨flag1,next⟩,called,hnext⟩ := WP.spec_imp_exists spec
    dsimp only at hnext
    obtain ⟨out,tail⟩ := ih flag1 next (by omega)
    refine ⟨out,?_⟩
    rw [state_only_poseidon.external_local_packed_raw_loop0_loop0.eq_def,if_pos h]
    have assoc : (do
      let p ← (do
        let a ← Array.index_usize table row
        let i ← Array.index_usize a limb
        let b ← state_only_poseidon.EXTERNAL_LOCAL_LIMB_MODULUS_BOUND
        let next ← limb+1#usize
        ok (flag && (i<b),next))
      state_only_poseidon.external_local_packed_raw_loop0_loop0 table p.1 row p.2)=ok out := by
      rw [called,bind_tc_ok,tail]
    simpa only [bind_assoc_eq,bind_tc_ok] using assoc
#print axioms inner
end AspisR1.NDE_PackedScan
end
