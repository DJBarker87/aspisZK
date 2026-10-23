import S2A_BorrowInversion

/-! Contiguous native library traces. In particular a decoder/allocator/child
transition may NOT be silently omitted from `world`: its correspondence is a
separate enclosing-caller obligation. Every equation uses the same `world`.
This module does not assert existence of an adapter execution certificate. -/
set_option autoImplicit false
namespace AspisR1.S2A
open S2Trust

def NoWrite : Op → Prop
  | .write _ _ _ => False
  | _ => True

/-- Model shape lemma: borrow, move, read and drop do not change any payload. -/
theorem payload_frame {F : Type} (s : Heap F) (op : Op) (readonly : NoWrite op) :
    (run s op).1.payload = s.payload := by
  cases op with
  | shared a t o => dsimp [run]; split <;> rfl
  | exclusive a t o => dsimp [run]; split <;> rfl
  | deref t => dsimp [run]; split <;> rfl
  | write t i v => cases readonly
  | move t o => rfl
  | drop t => dsimp [run]; split <;> rfl
  | errorMoveDrop => rfl

def shadow {F : Type} (initial : Heap F) (operation : Nat → Op) : Nat → Heap F
  | 0 => initial
  | n+1 => (run (shadow initial operation n) (operation n)).1

/-- Successful AND rejected primitive transitions are simulated in their actual
order. The shadow is computed from the fixed initial state, not independently
chosen at each cut. Runtime validity/enabledness remain explicit admission. -/
theorem native_prefix {W F : Type} (L : Library W F)
    (trust : S2TrustedSdkBorrow L) (world : Nat → W) (initial : Heap F)
    (operation : Nat → Op) (reply : Nat → Reply) (n : Nat)
    (related : L.related (world 0) initial)
    (admitted : ∀ i, i < n → Valid (shadow initial operation i) ∧
      Enabled (shadow initial operation i) (operation i))
    (executed : ∀ i, i < n → L.run (world i) (operation i) = (world (i+1), reply i))
    (readonly : ∀ i, i < n → NoWrite (operation i)) :
    L.related (world n) (shadow initial operation n) ∧
      (shadow initial operation n).payload = initial.payload := by
  induction n with
  | zero => exact ⟨related, rfl⟩
  | succ n ih =>
    obtain ⟨before, frame⟩ := ih
      (fun i hi => admitted i (Nat.lt_trans hi (Nat.lt_succ_self n)))
      (fun i hi => executed i (Nat.lt_trans hi (Nat.lt_succ_self n)))
      (fun i hi => readonly i (Nat.lt_trans hi (Nat.lt_succ_self n)))
    have last := actual_step L trust (world n) (world (n+1))
      (shadow initial operation n) (operation n) (reply n) before
      (admitted n (Nat.lt_succ_self n)).1 (admitted n (Nat.lt_succ_self n)).2
      (executed n (Nat.lt_succ_self n))
    refine ⟨last.2, ?_⟩
    change (run (shadow initial operation n) (operation n)).1.payload = initial.payload
    rw [payload_frame _ _ (readonly n (Nat.lt_succ_self n)), frame]

/-- Whole-payload original-input identity at an actual shared dereference after
that same contiguous native prefix. No post-native allocation read, hash
identity, independent decoder run, or selected-coordinate conclusion is used. -/
theorem original_shared_read {W F : Type} (L : Library W F)
    (trust : S2TrustedSdkBorrow L) (world : Nat → W) (initial : Heap F)
    (operation : Nat → Op) (reply : Nat → Reply) (n token : Nat)
    (after : W) (g : Guard) (bytes : Payload)
    (related : L.related (world 0) initial)
    (admitted : ∀ i, i < n → Valid (shadow initial operation i) ∧
      Enabled (shadow initial operation i) (operation i))
    (executed : ∀ i, i < n → L.run (world i) (operation i) = (world (i+1), reply i))
    (readonly : ∀ i, i < n → NoWrite (operation i))
    (validAtCut : Valid (shadow initial operation n))
    (guard : lookup (shadow initial operation n) token = some g)
    (kind : g.kind = .shared)
    (readAtCut : L.run (world n) (.deref token) = (after, .payload bytes)) :
    bytes = initial.payload g.cell ∧
      L.related after (shadow initial operation n) := by
  obtain ⟨atCut, frame⟩ := native_prefix L trust world initial operation reply n
    related admitted executed readonly
  obtain ⟨read, post⟩ := shared_read L trust (world n) after
    (shadow initial operation n) token g bytes atCut validAtCut guard kind readAtCut
  exact ⟨read.trans (congrFun frame g.cell), post⟩

#print axioms payload_frame
#print axioms native_prefix
#print axioms original_shared_read
end AspisR1.S2A
