import NMX_SourceModel
set_option autoImplicit false
namespace NMX_FreshOwners
open Aeneas Aeneas.Std NMX_OwnedPackets NMX_SourceModel
/-- A nominal owner supply above every retained input owner. This does not
assert native allocation; the std interpretation must bind the supply. -/
def ceiling : List Nat → Nat
 | [] => 0
 | n :: rest => max n (ceiling rest)
def owners (prior : List Nat) : Owners :=
 let base := ceiling prior + 1
 ⟨base,base+1,base+2,base+3⟩

theorem bound (prior : List Nat) (n : Nat) (member : n ∈ prior) : n ≤ ceiling prior := by
 induction prior with
 | nil => cases member
 | cons a rest ih =>
   rcases List.mem_cons.mp member with same | tail
   · subst n; exact Nat.le_max_left _ _
   · exact Nat.le_trans (ih tail) (Nat.le_max_right _ _)

theorem distinct (prior : List Nat) :
 [(owners prior).master,(owners prior).checkpoint,(owners prior).lane,(owners prior).snapshot].Nodup := by
 simp [owners] <;> omega

theorem fresh (prior : List Nat) (n : Nat)
 (member : n ∈ [(owners prior).master,(owners prior).checkpoint,(owners prior).lane,(owners prior).snapshot]) :
 n ∉ prior := by
 intro old
 have hb := bound prior n old
 simp [owners] at member
 rcases member with rfl | rfl | rfl | rfl <;> omega

/-- All four full payloads remain in the SAME returned packet. -/
theorem auth (prior : List Nat) (mk ck lk : Array U8 32#usize)
 (master : Master) (checkpoint : Checkpoint) (lane : Lane) (snapshot : Snapshot) :
 (Auth.mk mk ck lk ⟨(owners prior).master,master⟩ ⟨(owners prior).checkpoint,checkpoint⟩
  ⟨(owners prior).lane,lane⟩ ⟨(owners prior).snapshot,snapshot⟩).Fresh prior :=
 ⟨distinct prior,fresh prior⟩
#print axioms bound
#print axioms distinct
#print axioms fresh
#print axioms auth
end NMX_FreshOwners
