import NCD_KMX_CopyMeaning
set_option autoImplicit false
namespace NCD_FillFrame
/-- Full allocation carrier, including its initialized length and unchanged
address/capacity. Native validity and ownership are separate obligations. -/
structure Carrier (α : Type) where
  storage : Nat → α
  address : Nat
  capacity : Nat
  length : Nat

def step {α : Type} (s : Carrier α) (value : α) : Carrier α :=
  { s with storage := KMX_CopyMeaning.write s.storage (s.address+s.length) value,
           length := s.length+1 }

/-- Local native write observations on the SAME allocation; no whole output
or successful resize/model execution is assumed. -/
inductive Trace {α : Type} (value : α) : Carrier α → Nat → Carrier α → Prop
  | zero (s) : Trace value s 0 s
  | next {s middle final count} : Trace value s count middle →
      middle.length < middle.capacity → final = step middle value →
      Trace value s (count+1) final

theorem metadata {α : Type} {value : α} {s out : Carrier α} {n : Nat}
    (trace : Trace value s n out) :
    out.address=s.address ∧ out.capacity=s.capacity ∧ out.length=s.length+n := by
  induction trace with
  | zero => exact ⟨rfl,rfl,by omega⟩
  | @next middle final count trace spare same ih =>
    subst final
    simp only [step]
    exact ⟨ih.1,ih.2.1,by omega⟩

/-- Compose selected native windows over the full unchanged carrier using
KMX's already proved indexed-write law. -/
theorem storage {α : Type} {value : α} {s out : Carrier α} {n : Nat}
    (trace : Trace value s n out) (k : Nat) :
    out.storage k =
      if s.address+s.length ≤ k ∧ k < s.address+s.length+n then value else s.storage k := by
  induction trace with
  | zero =>
    have h : ¬(s.address+s.length ≤ k ∧ k < s.address+s.length+0) := by omega
    simp only [if_neg h]
  | @next middle final count trace spare same ih =>
    have fields :=  metadata trace
    subst final
    change KMX_CopyMeaning.write middle.storage (middle.address+middle.length) value k = _
    simp only [KMX_CopyMeaning.write,fields.1,fields.2.2]
    by_cases hit : k=s.address+(s.length+count)
    · have yes : s.address+s.length ≤ k ∧ k < s.address+s.length+(count+1) := by omega
      simp only [if_pos hit,if_pos yes]
    · rw [if_neg hit,ih]
      have eq : (s.address+s.length ≤ k ∧ k < s.address+s.length+count) ↔
          (s.address+s.length ≤ k ∧ k < s.address+s.length+(count+1)) := by omega
      rw [eq]

theorem initialized14759 {α : Type} {value : α} {s out : Carrier α}
    (empty : s.length=0) (capacity : s.capacity=14759)
    (trace : Trace value s 14759 out) :
    out.address=s.address ∧ out.capacity=14759 ∧ out.length=14759 ∧
    (∀ k, out.storage k=if s.address≤k ∧ k<s.address+14759 then value else s.storage k) := by
  have fields :=  metadata trace
  refine ⟨fields.1,fields.2.1.trans capacity,by omega,?_⟩
  intro k
  simpa only [empty,Nat.add_zero] using storage trace k

#print axioms metadata
#print axioms storage
#print axioms initialized14759
end NCD_FillFrame
