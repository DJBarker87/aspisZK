import NMX_SourceProgram
set_option autoImplicit false
noncomputable section
namespace NMX_ControlLaws
open Aeneas Aeneas.Std AdapterRw NMX_OwnedPackets NMX_Program
/-- Isolated source-term guard, before any outcome erasure or child call. -/
theorem account_count (ops : Ops) (program : solana_pubkey.Pubkey)
 (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey)
 (lane : U8) (slot : U64) (count : Slice.len accounts ≠ 7#usize) :
 NMX_SourceProgram.auth ops program accounts pool lane slot =
 if Slice.len accounts < 7#usize then Program.reject .NotEnoughAccountKeys
 else Program.reject .InvalidArgument := by
 simp [NMX_SourceProgram.auth, count]
/-- General symbolic distribution; prevents splitting an unknown outcome in
place of the controlling source condition. -/
theorem eval_if {W E A : Type} (handler : Handler W E) (p : Prop) [Decidable p]
 (yes no : Program A) (before : W) :
 eval handler (if p then yes else no) before =
 if p then eval handler yes before else eval handler no before := by
 by_cases h : p <;> simp only [h,↓reduceIte]
#print axioms account_count
#print axioms eval_if
end NMX_ControlLaws
end
