import NNH_AuthSeeds
import NGL_ArrayEquality
set_option autoImplicit false
noncomputable section
namespace NNH_AuthSlotFacts
open Aeneas Aeneas.Std AdapterRw
attribute [local instance] Classical.propDecidable

theorem mask (base : Ops) (env : RSL.Env) : (NNH_Tx2ModelSlots.install base env).op16=.ok 255#u8 := rfl
theorem fromBytes (base : Ops) (env : RSL.Env) (k : solana_pubkey.Pubkey) :
 (NNH_Tx2ModelSlots.install base env).op37 k=.ok k := rfl
theorem bytes (base : Ops) (env : RSL.Env) (k : solana_pubkey.Pubkey) :
 (NNH_Tx2ModelSlots.install base env).op39 k=.ok k := rfl
theorem asRef (base : Ops) (env : RSL.Env) (k : solana_pubkey.Pubkey) :
 (NNH_Tx2ModelSlots.install base env).op40 k=.ok (Array.to_slice k) := rfl

theorem ne_self (base : Ops) (env : RSL.Env) (k : solana_pubkey.Pubkey) :
 core.cmp.PartialEq.ne.trait_default
  (solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey (NNH_Tx2ModelSlots.install base env)) k k=.ok false := by
 have eq : (solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey (NNH_Tx2ModelSlots.install base env)).eq k k=.ok true := by
  change Result.ok (decide (k=k))=Result.ok true
  simp only [decide_true]
 unfold core.cmp.PartialEq.ne.trait_default core.cmp.PartialEq.ne.default
 rw [eq]
 rfl
#print axioms mask
#print axioms fromBytes
#print axioms bytes
#print axioms asRef
#print axioms ne_self
end NNH_AuthSlotFacts
