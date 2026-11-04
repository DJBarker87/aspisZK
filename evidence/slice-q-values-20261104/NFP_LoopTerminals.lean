import NFG_QueryLoopSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFP_LoopTerminals
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2 NFG_QueryLoopDefs

theorem error (query : Query) (finish : Usize) (err : verifier.Error) :
 step query finish (.Err err) = ok (done (.Err err)) := rfl

theorem stopped (query : Query) (finish : Usize) (a : A) (b : B)
 (halt : a.next ≥ finish) :
 step query finish (.Ok (a,b)) = ok (done (.Ok (a,b))) := by
 simp only [step,if_pos halt]

/-- Nothing follows a rejected child: every remaining finite suffix is the
same Err, with no further query call. -/
theorem rejected (query : Query) (finish : Usize) (a : A) (b : B)
 (err : verifier.Error) (fuel : Nat) (active : ¬a.next ≥ finish)
 (reply : query a b = ok (.Err err)) :
 run query finish (fuel+1) (.Ok (a,b)) = ok (.Err err) := by
 simp only [run,if_neg active,reply,bind_tc_ok]
 cases fuel <;> rfl

/-- Machine failure and divergence terminate before the next loop body. -/
theorem failed (query : Query) (finish : Usize) (a : A) (b : B)
 (err : Aeneas.Std.Error) (fuel : Nat) (active : ¬a.next ≥ finish)
 (reply : query a b = fail err) :
 run query finish (fuel+1) (.Ok (a,b)) = fail err := by
 simp only [run,if_neg active,reply,bind_tc_fail]

theorem diverged (query : Query) (finish : Usize) (a : A) (b : B)
 (fuel : Nat) (active : ¬a.next ≥ finish) (reply : query a b = div) :
 run query finish (fuel+1) (.Ok (a,b)) = div := by
 simp only [run,if_neg active,reply,bind_tc_div]
#print axioms error
#print axioms stopped
#print axioms rejected
#print axioms failed
#print axioms diverged
end AspisR1.NFP_LoopTerminals
end
