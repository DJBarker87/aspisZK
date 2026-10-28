import AspisR1TerminalDecoder.Funs
set_option autoImplicit false
noncomputable section
namespace NBG_Atomic
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder

/-- Generic Copy payload is returned unchanged. The guard caller must prove
its fixed-width conversion succeeds; no arbitrary Err is treated as success. -/
theorem unwrap_ok {T : Type} (copy : core.marker.Copy T) (value : T) :
    atomic_statement.unwrap_fixed_slice copy (.Ok value) = ok value := rfl

theorem unwrap_err {T : Type} (copy : core.marker.Copy T)
    (error : core.array.TryFromSliceError) :
    atomic_statement.unwrap_fixed_slice copy (.Err error) = fail .panic := rfl

/-- Complete field projection, including every byte and raw limb; no
canonicality or valid-statement precondition is required. -/
theorem transfer_projection (p : pool_v1.payment_relation.PoolV1PrivateTransferPublicV1) :
    pool_v1.payment_relation.transfer_common p = ok
      ({pool := p.pool, deployment_domain := p.deployment_domain,
        anchor_sequence := p.anchor_sequence, anchor_root := p.anchor_root,
        nullifier := p.nullifier, asset_id := p.asset_id} :
        pool_v1.payment_relation.CommonPublicV1) := rfl

theorem withdrawal_projection (p : pool_v1.payment_relation.PoolV1WithdrawalPublicV1) :
    pool_v1.payment_relation.withdrawal_common p = ok
      ({pool := p.pool, deployment_domain := p.deployment_domain,
        anchor_sequence := p.anchor_sequence, anchor_root := p.anchor_root,
        nullifier := p.nullifier, asset_id := p.asset_id} :
        pool_v1.payment_relation.CommonPublicV1) := rfl

#print axioms unwrap_ok
#print axioms unwrap_err
#print axioms transfer_projection
#print axioms withdrawal_projection
end NBG_Atomic

namespace NBG_Atomic
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
/-- Raw limbs are admitted. A false test is a normal false result, not a
canonical-input assumption. The eight checks keep source short-circuit order. -/
theorem digest_canonical (a b c d e f g h : U32) :
    pool_v1.payment_relation.digest_is_canonical
      (Array.make 8#usize [a,b,c,d,e,f,g,h]) =
    ok (if a < 2147483647#u32 then
      if b < 2147483647#u32 then
        if c < 2147483647#u32 then
          if d < 2147483647#u32 then
            if e < 2147483647#u32 then
              if f < 2147483647#u32 then
                if g < 2147483647#u32 then
                  if h < 2147483647#u32 then true else false
                else false
              else false
            else false
          else false
        else false
      else false
    else false) := by
  simp [pool_v1.payment_relation.digest_is_canonical, Array.index_usize,
    Array.make, aspis_core.field.P]
  repeat' split
  all_goals simp_all

#print axioms digest_canonical
end NBG_Atomic

namespace NBG_Atomic
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder

theorem m31_decode (bytes : Array U8 4#usize) :
    aspis_core.field.M31.from_le_bytes bytes =
      ok (let word := core.num.U32.from_le_bytes bytes
          if word >= 2147483647#u32 then none else some word) := by
  simp only [aspis_core.field.M31.from_le_bytes, aspis_core.field.P, lift, bind_tc_ok]
  split <;> rfl

#print axioms m31_decode
end NBG_Atomic
