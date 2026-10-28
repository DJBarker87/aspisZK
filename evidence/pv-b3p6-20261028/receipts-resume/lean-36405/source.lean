import PV_B3P_Schedule133
namespace PV_B3P_EndpointResult133
open PV_B3P_Schedule133
set_option autoImplicit false

theorem checked_success (links : List Link) (n : Nat) (hlen : links.length = n)
    (hcap : checkEndpoints links [] [] = .ok ()) : checked n links = .ok links := by
  simp [checked,hlen,hcap]

theorem checked_shape (links : List Link) (n : Nat) (hlen : links.length ≠ n) :
    checked n links = .error .shape := by
  simp [checked,hlen]

theorem checked_capacity (links : List Link) (n row : Nat) (hlen : links.length = n)
    (hcap : checkEndpoints links [] [] = .error (.endpointCapacity row)) :
    checked n links = .error (.endpointCapacity row) := by
  simp [checked,hlen,hcap]

theorem check_bounds (links : List Link) (ps cs : List Nat)
    (h : checkEndpoints links ps cs = .ok ()) :
    ∀ x ∈ links, x.producer < 1024 ∧ x.consumer < 1024 := by
  induction links generalizing ps cs with
  | nil => simp
  | cons head tail ih =>
    simp only [checkEndpoints] at h
    split at h
    · contradiction
    · split at h
      · contradiction
      · rename_i hp hc
        have hp' : head.producer < 1024 := by simpa using (Bool.or_eq_false_iff.mp hp).1
        have hc' : head.consumer < 1024 := by simpa using (Bool.or_eq_false_iff.mp hc).1
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨hp',hc'⟩
        · exact ih _ _ h x hx

#print axioms checked_success
#print axioms checked_shape
#print axioms checked_capacity
#print axioms check_bounds
end PV_B3P_EndpointResult133
