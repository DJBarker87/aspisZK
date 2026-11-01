import KMX_CopyMeaning
set_option autoImplicit false
namespace NEJ_CommonFrame
open KMX_CopyMeaning

/-- Source-order write windows of frozen payment_relation::encode_common.
Digest computations precede their respective copy windows and are separate
child obligations. This describes byte writes only. -/
def windows : List (Nat × Nat) :=
  [(0,4),(4,1),(5,1),(6,1),(8,32),(40,32),(72,8),(80,32),(112,32),(144,4)]

def touched (ws : List (Nat × Nat)) (k : Nat) : Prop :=
  ∃ w ∈ ws, w.1 ≤ k ∧ k < w.1 + w.2

instance (ws : List (Nat × Nat)) (k : Nat) : Decidable (touched ws k) :=
  inferInstanceAs (Decidable (∃ w ∈ ws, w.1 ≤ k ∧ k < w.1 + w.2))

def run {α : Type} (src dst : Nat → α) : List (Nat × Nat) → Nat → α
  | [] => dst
  | w :: ws => run src (loop src dst w.1 w.2) ws

/-- Arbitrary indexed prestate; no whole-buffer reduction or native unwinding. -/
theorem run_spec {α : Type} (src dst : Nat → α) (ws : List (Nat × Nat)) (k : Nat) :
    run src dst ws k = if touched ws k then src k else dst k := by
  induction ws generalizing dst with
  | nil => simp [run, touched]
  | cons w ws ih =>
    rw [run, ih, loop_spec]
    by_cases ht : touched ws k
    · have h : touched (w :: ws) k := by
        obtain ⟨v,hv,h⟩ := ht
        exact ⟨v,List.mem_cons_of_mem w hv,h⟩
      simp [ht,h]
    · by_cases hw : w.1 ≤ k ∧ k < w.1 + w.2
      · have h : touched (w :: ws) k := ⟨w,List.mem_cons_self,hw⟩
        simp [ht,hw,h]
      · have h : ¬ touched (w :: ws) k := by
          rintro ⟨v,hv,hv'⟩
          rcases List.mem_cons.mp hv with heq | hm
          · subst v; exact hw hv'
          · exact ht ⟨v,hm,hv'⟩
        simp [ht,hw,h]

/-- Exact union of the ten frozen write ranges, including reserved-byte gaps. -/
theorem touched_windows (k : Nat) :
    touched windows k ↔ k < 7 ∨ (8 ≤ k ∧ k < 148) := by
  simp only [touched, windows, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨w,hw,hr⟩
    rcases hw with h | h | h | h | h | h | h | h | h | h
    all_goals subst w; dsimp at hr; omega
  · intro h
    rcases h with h | h
    · by_cases h0 : k < 4
      · exact ⟨(0,4),by simp,by dsimp; omega⟩
      · by_cases h4 : k = 4
        · exact ⟨(4,1),by simp,by dsimp; omega⟩
        · by_cases h5 : k = 5
          · exact ⟨(5,1),by simp,by dsimp; omega⟩
          · exact ⟨(6,1),by simp,by dsimp; omega⟩
    · by_cases h40 : k < 40
      · exact ⟨(8,32),by simp,by dsimp; omega⟩
      · by_cases h72 : k < 72
        · exact ⟨(40,32),by simp,by dsimp; omega⟩
        · by_cases h80 : k < 80
          · exact ⟨(72,8),by simp,by dsimp; omega⟩
          · by_cases h112 : k < 112
            · exact ⟨(80,32),by simp,by dsimp; omega⟩
            · by_cases h144 : k < 144
              · exact ⟨(112,32),by simp,by dsimp; omega⟩
              · exact ⟨(144,4),by simp,by dsimp; omega⟩

theorem common_bytes {α : Type} (src dst : Nat → α) (k : Nat) :
    run src dst windows k =
      if k < 7 ∨ (8 ≤ k ∧ k < 148) then src k else dst k := by
  simp only [run_spec, touched_windows]

/-- Byte 7 and the entire suffix from 148 survive arbitrary child reply bytes. -/
theorem reserved_frame {α : Type} (src dst : Nat → α) (k : Nat)
    (outside : k = 7 ∨ 148 ≤ k) : run src dst windows k = dst k := by
  rw [common_bytes, if_neg]
  omega

/-- Distinct windows can be joined without assuming their initial bytes zero. -/
theorem window_disjoint {α : Type} (src dst : Nat → α) (a n b m k : Nat)
    (inside : b ≤ k ∧ k < b + m) (disjoint : a+n ≤ b ∨ b+m ≤ a) :
    loop src dst a n k = dst k := by
  apply copy_frame
  omega

#print axioms run_spec
#print axioms touched_windows
#print axioms common_bytes
#print axioms reserved_frame
#print axioms window_disjoint
end NEJ_CommonFrame
