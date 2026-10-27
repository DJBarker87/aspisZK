import FJe_RawLocalCanon
import FJb_ExternalExact
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJe_PackedLoopCanonical
open Aeneas Aeneas.Std Result WP FIq_Native
open FIv_NativeArithmetic (NQ)
open FIw_ArrayValue (canonical)
/-- Canonicality of the original four-group traversal,using the canonical
result of its actual local helper. No local output VALUE is assumed. -/
theorem value (n : Nat) (g : Usize) (s : Array NQ 16#usize)
    (p out : Array NQ 4#usize) (hspan : g.val+n=4) (hp : canonical p)
    (run : state_only_poseidon.external_linear_packed_loop s p g=ok out) :
    canonical out := by
  induction n generalizing g p with
  | zero =>
    have hno : ¬g<4#usize := by scalar_tac
    rw [state_only_poseidon.external_linear_packed_loop.eq_def,if_neg hno] at run
    have same : p=out := Result.ok.inj run
    subst out
    exact hp
  | succ n ih =>
    have hg : g.val<(4#usize).val := by change g.val<4;omega
    have hlt : g<4#usize := by scalar_tac
    rw [state_only_poseidon.external_linear_packed_loop.eq_def,if_pos hlt] at run
    obtain ⟨start,_,run⟩ := FIv_Map.bind_success _ _ _ run
    obtain ⟨q0,_,run⟩ := FIv_Map.bind_success _ _ _ run
    obtain ⟨i1,_,run⟩ := FIv_Map.bind_success _ _ _ run
    obtain ⟨q1,_,run⟩ := FIv_Map.bind_success _ _ _ run
    obtain ⟨i2,_,run⟩ := FIv_Map.bind_success _ _ _ run
    obtain ⟨q2,_,run⟩ := FIv_Map.bind_success _ _ _ run
    obtain ⟨i3,_,run⟩ := FIv_Map.bind_success _ _ _ run
    obtain ⟨q3,_,run⟩ := FIv_Map.bind_success _ _ _ run
    obtain ⟨q,rq,run⟩ := FIv_Map.bind_success _ _ _ run
    obtain ⟨next,rnext,run⟩ := FIv_Map.bind_success _ _ _ run
    obtain ⟨g1,rg1,run⟩ := FIv_Map.bind_success _ _ _ run
    have cq := FJe_RawLocalCanon.local_value (Array.make 4#usize [q0,q1,q2,q3]) q rq
    have cn := (FIw_ArrayValue.update p next g q hg hp cq rnext).1
    have hspec : (g+1#usize : Result Usize) ⦃z=>z.val=g.val+1⦄ := by
      apply UScalar.add_spec
      scalar_tac
    obtain ⟨g2,rg2,vg⟩ := WP.spec_imp_exists hspec
    have eg : g1=g2 := Result.ok.inj (rg1.symm.trans rg2)
    subst g2
    exact ih g1 next (by omega) cn run
#print axioms value
end AspisR1.FJe_PackedLoopCanonical
end
