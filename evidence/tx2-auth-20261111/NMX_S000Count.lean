import NMX_ControlLaws
import NMX_ValueLink
set_option autoImplicit false
noncomputable section
namespace NMX_S000Count
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_Program NMX_SourceModel
/-- Split the controlling guard before interpreting the outcome. No child is
called and the complete returned frame and empty prefix remain explicit. -/
theorem frame {W : Type} (ops : Ops) (program : solana_pubkey.Pubkey)
 (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey)
 (lane : U8) (slot : U64) (handler : Handler W NLM_Auth233.Event) (before : W)
 (count : Slice.len accounts ≠ 7#usize) :
 eval handler (NMX_SourceProgram.auth ops program accounts pool lane slot) before =
 .returned (.Err (if Slice.len accounts < 7#usize then .NotEnoughAccountKeys else .InvalidArgument)) before [] := by
 rw [NMX_ControlLaws.account_count ops program accounts pool lane slot count,
     NMX_ControlLaws.eval_if]
 by_cases short : Slice.len accounts < 7#usize <;> simp only [short,↓reduceIte,eval]

theorem emitted (ops : Ops) (owners : Owners) (program : solana_pubkey.Pubkey)
 (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey)
 (lane : U8) (slot : U64) (count : Slice.len accounts ≠ 7#usize) :
 NMX_ValueLink.erase (eval (source ops owners)
  (NMX_SourceProgram.auth ops program accounts pool lane slot) ()) =
 NMX_Emitted.auth ops ops.op50
  (r1_pool_adapter.owned.authenticate_invariant_release_registry ops)
  program accounts pool lane slot := by
 rw [frame ops program accounts pool lane slot (source ops owners) () count]
 simp only [NMX_Emitted.auth,count,↓reduceIte]
 by_cases short : Slice.len accounts < 7#usize <;>
  simp only [short,↓reduceIte,NMX_ValueLink.erase]
#print axioms frame
#print axioms emitted
end NMX_S000Count
end
