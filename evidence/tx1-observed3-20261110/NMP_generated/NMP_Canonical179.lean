import NMP_Expansion179
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMP_Canonical179
open Aeneas Aeneas.Std Result
open NFU_Retarget
/-- A predicate on the row's OWN bytes, not a successful check Result.
The upstream canonical_scan producer must establish this at prepare's input. -/
def Canonical (bytes : Slice U8) : Prop :=
 ∀ i, i<bytes.val.length/16 → LPl.Check.predicate bytes.val i=true
private theorem trace_none (p : Nat → Bool) (count : Nat)
 (all : ∀ i,i<count → p i=true) : ∀ n i, count-i=n → i≤count →
 LPl.Scan.Trace p count i none := by
 intro n
 induction n with
 | zero => intro i remaining bound;exact .done i (by omega)
 | succ n ih =>
  intro i remaining bound
  have live : i<count := by omega
  exact .next i live (all i live) none (ih (i+1) (by omega) (by omega))
theorem check (bytes : Slice U8) (canonical : Canonical bytes) :
 NFU_Retarget.compact.check_values bytes=ok (.Ok ()) := by
 have trace := trace_none (LPl.Check.predicate bytes.val) (bytes.val.length/16)
  canonical (bytes.val.length/16) 0 (by omega) (by omega)
 exact NFU_CompactLeaves.check_result bytes none trace
#print axioms trace_none
#print axioms check
#print check
end AspisR1.NMP_Canonical179
end
