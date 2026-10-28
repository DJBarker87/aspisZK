import R1Z.PV_OWN_Heap
set_option autoImplicit false
namespace R1Z.PV_OWN_Bytes
open PV_OWN_Heap
abbrev Bytes := Nat → Option UInt8
/-- Relative byte offsets; padding is allowed to remain uninitialized. -/
def overwrite (old : Bytes) (start width : Nat) (value : Bytes) : Bytes :=
  fun i => if start≤i ∧ i<start+width then value (i-start) else old i

def store (c : Cell) (start width : Nat) (value : Bytes) : Cell :=
  {c with contents := overwrite c.contents start width value}

def Fits (c : Cell) (start width : Nat) : Prop := start+width≤c.size

theorem inside (old value : Bytes) (start width i : Nat) (h:i<width) :
    overwrite old start width value (start+i)=value i := by
  simp [overwrite,show start≤start+i by omega,show start+i<start+width by omega]
theorem outside (old value : Bytes) (start width i : Nat)
    (h:i<start ∨ start+width≤i) : overwrite old start width value i=old i := by
  have hh:¬(start≤i ∧ i<start+width) := by omega
  simp [overwrite,hh]
theorem empty (old value : Bytes) (start : Nat) : overwrite old start 0 value=old := by
  funext i; simp [overwrite]
theorem shadow (old a b : Bytes) (start width : Nat) :
    overwrite (overwrite old start width a) start width b=overwrite old start width b := by
  funext i; by_cases h:start≤i ∧ i<start+width <;> simp [overwrite,h]
theorem store_header (c : Cell) (s n : Nat) (v : Bytes) :
    (store c s n v).size=c.size ∧ (store c s n v).alignment=c.alignment ∧
    (store c s n v).capacity=c.capacity ∧ (store c s n v).owner=c.owner ∧
    (store c s n v).live=c.live := ⟨rfl,rfl,rfl,rfl,rfl⟩
#print axioms inside
#print axioms outside
#print axioms empty
#print axioms shadow
#print axioms store_header
end R1Z.PV_OWN_Bytes
