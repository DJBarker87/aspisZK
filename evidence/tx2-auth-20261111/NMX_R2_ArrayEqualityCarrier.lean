import NMX_R2_KeyCarrier
import NMX_R2_PrimitiveInstall
import NGL_ArrayEquality
set_option autoImplicit false
noncomputable section
namespace NMX_R2_ArrayEqualityCarrier
open Aeneas Aeneas.Std Result AdapterRw NMX_R2_Carrier
attribute [local instance] Classical.propDecidable

theorem array_ne (a b : Array U8 32#usize) :
 core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 a b =
 ok (decide (key a ≠ key b)) := by
 rw [NGL_ArrayEquality.ne_value]
 simp only [decide_not,NMX_R2_KeyCarrier.key_equal]

theorem key_ne (base : Ops) (env : RSL.Env) (a b : solana_pubkey.Pubkey) :
 core.cmp.PartialEq.ne.trait_default
  (solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey (NMX_R2_PrimitiveInstall.install base env)) a b =
 ok (decide (key a ≠ key b)) := by
 have comparison := NGL_ReadonlyModel.comparison (NMX_R2_PrimitiveInstall.install base env) a b
 change core.cmp.impls.PartialEqShared.ne
   (solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey
    (NGL_ReadonlyModel.install (NMX_R2_PrimitiveInstall.install base env))) a b = _
 rw [comparison]
 simp only [decide_not,NMX_R2_KeyCarrier.key_equal]
#print axioms array_ne
#print axioms key_ne
end NMX_R2_ArrayEqualityCarrier
end
