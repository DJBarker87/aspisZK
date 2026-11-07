import NMT_R2_Base
set_option autoImplicit false
namespace NMT_R2_AllocCollapse
open RSL
/-- A finite event-free sequence of reached allocation sites. Count is
symbolic: no concrete decoder allocation graph is kernel-normalized. -/
def sites : Nat → Spec Unit
 | 0 => Spec.pure ()
 | n+1 => Spec.bind Spec.alloc (fun _ => sites n)

theorem sites_positive (n : Nat) (env : Env) (o : Obs Unit) :
 sites (n+1) env o ↔ o = ⟨.ret (),[]⟩ ∨ o = ⟨.abort,[]⟩ := by
 induction n with
 | zero =>
  unfold sites
  rw [Spec.bind_two _ _ env () (fun _ => Iff.rfl)]
  rfl
 | succ n ih =>
  change Spec.bind Spec.alloc (fun _ => sites (n+1)) env o ↔ _
  rw [Spec.bind_two _ _ env () (fun _ => Iff.rfl),ih]
  simp only [or_assoc,or_self]

/-- Exact collapse, including runs that allocate and THEN return a decoder Err.
This equality does not turn early rejection into a possible abort. -/
theorem sites_collapse (n : Nat) : sites n = Spec.allocIf (n != 0) := by
 funext env o
 apply propext
 cases n with
 | zero => rfl
 | succ n =>
  change sites (n+1) env o ↔ Spec.alloc env o
  exact sites_positive n env o

/-- Appending a fixed return after any finite reached allocation sequence has
exactly the canonical internal-decoder allocation prefix and that full value. -/
theorem result_collapse {A : Type} (n : Nat) (result : A) :
 Spec.bind (sites n) (fun _ => Spec.pure result) =
 Spec.bind (Spec.allocIf (n != 0)) (fun _ => Spec.pure result) := by
 rw [sites_collapse]
#print axioms sites_positive
#print axioms sites_collapse
#print axioms result_collapse
end NMT_R2_AllocCollapse
