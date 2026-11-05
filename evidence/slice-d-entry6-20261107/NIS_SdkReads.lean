import NIS_AdmissionSdk
import NHJ_SdkBorrowPacket
set_option autoImplicit false
namespace AspisR1.NIS_SdkReads
open S2Trust S2W_D189Entry S2W_D189Consolidation

/-- The actual three primitive library calls of one snapshot read. No Vec
allocation, native ABI association, or parent output is asserted here. -/
def Read {W : Type} (L : Library W (Nat → Record)) (e : Entry)
    (a : Nat) (w next : W) : Prop :=
  ∃ entered viewed,
    L.run w (.shared a 0 0) = (entered,.guard 0) ∧
    L.run entered (.deref 0) = (viewed,.payload (e.heap.payload (e.heap.accounts a).1)) ∧
    L.run viewed (.drop 0) = (next,.unit)

inductive Reads {W : Type} (L : Library W (Nat → Record)) (e : Entry) :
    W → List Nat → W → Prop
  | nil (w : W) : Reads L e w [] w
  | cons {w middle last : W} {a : Nat} {rest : List Nat} :
      Read L e a w middle → Reads L e middle rest last → Reads L e w (a::rest) last

theorem one {W : Type} (L : Library W (Nat → Record)) (sdk : S2TrustedSdkBorrow L)
    (e : Entry) (w : W) (n a : Nat) (admission : RuntimeEntrypointAdmission L e w n)
    (within : a < n) :
    ∃ next, Read L e a w next ∧ RuntimeEntrypointAdmission L e next n := by
  have low : 0 ≤ e.heap.counter (e.heap.accounts a).1 := by
    rw [admission.entry.counterZero a within]
  have high : e.heap.counter (e.heap.accounts a).1 < maxCounter := by
    rw [admission.entry.counterZero a within]
    simp only [maxCounter]
    omega
  obtain ⟨entered,viewed,next,acquired,dereferenced,dropped,related⟩ :=
    NHJ_SdkBorrowPacket.returning_shared L sdk w e.heap admission.related
      admission.entry.valid a 0 0 (NIS_AdmissionSdk.enabled L e w n a 0 0 admission within).1 low high
  exact ⟨next,⟨entered,viewed,acquired,dereferenced,dropped⟩,⟨admission.entry,related⟩⟩

/-- Repeated or aliased account handles are safe: every read/drop restores the
same admitted heap before the next operation. These are applications of the
named SDK/runtime contracts, not new native proofs of their internals. -/
theorem sequence {W : Type} (L : Library W (Nat → Record)) (sdk : S2TrustedSdkBorrow L)
    (e : Entry) (n : Nat) (ports : List Nat) (bounded : ∀ a ∈ ports, a < n)
    (w : W) (admission : RuntimeEntrypointAdmission L e w n) :
    ∃ next, Reads L e w ports next ∧ RuntimeEntrypointAdmission L e next n := by
  induction ports generalizing w with
  | nil => exact ⟨w,.nil w,admission⟩
  | cons a rest ih =>
    obtain ⟨middle,read,ready⟩ := one L sdk e w n a admission (bounded a (by simp))
    obtain ⟨last,reads,final⟩ := ih (fun b member => bounded b (by simp [member])) middle ready
    exact ⟨last,.cons read reads,final⟩

theorem seven {W : Type} (L : Library W (Nat → Record)) (sdk : S2TrustedSdkBorrow L)
    (e : Entry) (w : W) (admission : RuntimeEntrypointAdmission L e w 7) :
    ∃ next, Reads L e w (List.range 7) next ∧ RuntimeEntrypointAdmission L e next 7 :=
  sequence L sdk e 7 (List.range 7) (by intro a member; exact List.mem_range.mp member) w admission

theorem three_then_exclusive {W : Type} (L : Library W (Nat → Record)) (sdk : S2TrustedSdkBorrow L)
    (e : Entry) (w : W) (admission : RuntimeEntrypointAdmission L e w 3) :
    ∃ next, Reads L e w (List.range 3) next ∧
      Matches L next (.exclusive 2 0 0)
        (acquire e.heap (e.heap.accounts 2).1 0 0 .exclusive,.guard 0) := by
  obtain ⟨next,reads,ready⟩ :=
    sequence L sdk e 3 (List.range 3) (by intro a member; exact List.mem_range.mp member) w admission
  exact ⟨next,reads,NIS_AdmissionSdk.exclusive L sdk e next 3 2 0 0 ready (by omega)⟩

#print axioms one
#print axioms sequence
#print axioms seven
#print axioms three_then_exclusive
end AspisR1.NIS_SdkReads
