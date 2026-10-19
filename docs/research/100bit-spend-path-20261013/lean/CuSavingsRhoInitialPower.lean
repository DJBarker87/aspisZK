import CuSavingsRhoPrepared
import CuSavingsRhoAccumulatorNew

/-! Consume both actual initial source constructors in the checked power tail.
No input canonicality/counter premise is supplied. This does not replace the
unproved intervening complete query/coefficient/RHS source-context binding.
-/
set_option autoImplicit false
namespace AspisR1.CuSavingsRhoInitialPower
open Aeneas Aeneas.Std Result AspisR1RhoPowerTail
variable [AspisR1CuRho.HeapReserve] [PreparedCommon] [AspisR1CuRho.ScalarKBlocks]

theorem source_tail_success {H : Type} (D : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H)
    (scratch finalScratch : Array aspis_core.field.WideExact 29#usize)
    (p : verifier.Prepared) (a : verifier.Accumulator)
    (hp : gamma_new.Prepared.gamma_new_new D sem v hash scratch = .ok (.Ok p,finalScratch))
    (ha : verifier.Accumulator.new v.variant = .ok (.Ok a)) :
    ∃ out : verifier.Accumulator,
      power_tail p a = .ok out ∧ CuSavingsRhoPowerTail.Canonical out.power ∧
      out.next.val=1 ∧ out.weights=a.weights ∧ out.rhs=aspis_core.field.WideExact.ZERO := by
  have hrho := (CuSavingsRhoPrepared.source_success D sem v hash scratch finalScratch p hp).1
  obtain ⟨_,hpower,hnext,_,_,hrhs⟩ := CuSavingsRhoAccumulatorNew.source_success v.variant a ha
  obtain ⟨out,hrun,hcanonical,hincrement,_,hweights,hframe,_⟩ :=
    CuSavingsRhoPowerTail.source_success p a hpower hrho (by rw [hnext];decide)
  refine ⟨out,hrun,hcanonical,?_,hweights,hframe.trans hrhs⟩
  rw [hincrement,hnext]

#print axioms source_tail_success
end AspisR1.CuSavingsRhoInitialPower
