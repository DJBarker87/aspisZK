import NDO_JGj_PackedGroupTotal
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGj_PackedLoopTotal
open Aeneas Aeneas.Std Result WP FIq_Native
open FIw_ArrayValue (canonical)
open FJb_MatrixGroupStep (State)
open FJe_PackedGroupStep (Packed)
theorem source (n : Nat) (g : Usize) (s : State) (p : Packed)
    (hn : g.val+n=4) (hs : canonical s) (hp : canonical p) :
    ∃ out,state_only_poseidon.external_linear_packed_loop s p g=ok out ∧ canonical out := by
  induction n generalizing g p with
  | zero =>
    have h : ¬g<4#usize := by scalar_tac
    exact ⟨p,by rw [FJe_PackedGroupStep.unfold_loop,if_neg h],hp⟩
  | succ n ih =>
    have h : g<4#usize := by scalar_tac
    obtain ⟨p1,rp,cp⟩ := JGj_PackedGroupTotal.source s p g (by omega) hs hp
    have spec : (g+1#usize : Result Usize) ⦃ next=>next.val=g.val+1 ⦄ := by
      apply UScalar.add_spec
      scalar_tac
    obtain ⟨next,rn,vn⟩ := WP.spec_imp_exists spec
    obtain ⟨out,ro,co⟩ := ih next p1 (by omega) cp
    exact ⟨out,by rw [FJe_PackedGroupStep.unfold_loop,if_pos h,rp,bind_tc_ok,rn,bind_tc_ok,ro],co⟩
#print axioms source
end AspisR1.JGj_PackedLoopTotal
end
