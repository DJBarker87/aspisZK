import NBY_CarrierFold

set_option autoImplicit false
namespace AspisR1.NBY_RowCopy

def byteWindows {α : Type} (source memory : Nat → α) (base : Nat) : Nat → Nat → α
  | 0 => memory
  | n+1 => KMX_CopyMeaning.loop source (byteWindows source memory base n) (base+n) 1

/-- Compose one-byte windows over the same destination into the exact KMX
copy value law; each window consumes the previous window's poststate. -/
theorem windows_eq {α : Type} (source memory : Nat → α) (base count : Nat) :
    byteWindows source memory base count = KMX_CopyMeaning.loop source memory base count := by
  induction count with
  | zero => rfl
  | succ n ih =>
    rw [byteWindows,ih]
    exact NBV_CopyComposition.adjacent_windows source memory base n 1

/-- All bytes of a native row assignment and its complete outside frame are
obtained from those SAME one-byte updates, with an arbitrary surrounding array. -/
theorem row_cells {α : Type} (memory reply : Nat → α) (w j c : Nat) (byte : c < 32) :
    byteWindows (fun k => reply (k-32*w)) memory (32*w) 32 (32*j+c) =
      if j = w then reply c else memory (32*j+c) := by
  rw [windows_eq]
  by_cases same : j = w
  · subst j
    rw [if_pos rfl]
    exact NBV_CopyComposition.window_value memory reply (32*w) 32 c byte
  · rw [if_neg same]
    exact KMX_CopyMeaning.copy_frame _ memory (32*w) 32 (32*j+c) (by omega)

#print axioms windows_eq
#print axioms row_cells
end AspisR1.NBY_RowCopy
