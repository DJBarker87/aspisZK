import R1Z.PV_CB3_StagedByteShape
set_option autoImplicit false
namespace R1Z.PV_CB3_StagedByteWord
open Aeneas Aeneas.Std
open PV_CB3_StagedByteBits

theorem value (a b c d : U8) :
    (core.num.U32.from_le_bytes (Array.make 4#usize [a,b,c,d])).val =
      a.val + 256 * (b.val + 256 * (c.val + 256 * d.val)) := by
  have ha := PV_CB3_StagedLoadInspect.byte_bound a
  have hb := PV_CB3_StagedLoadInspect.byte_bound b
  have hc := PV_CB3_StagedLoadInspect.byte_bound c
  have hd := PV_CB3_StagedLoadInspect.byte_bound d
  have hd0 : (d.bv.setWidth 16).toNat = d.val := by
    rw [BitVec.toNat_setWidth_of_le (by decide),UScalar.bv_toNat]
  have hds : ((d.bv.setWidth 16) <<< 8).toNat = 256*d.val := by
    rw [shift_value _ (by rw [hd0]; change d.val*256<65536; omega),hd0]
    omega
  let cd : BitVec 24 := c.bv.setWidth 24 ||| (((d.bv.setWidth 16) <<< 8).setWidth 24)
  have hcd : cd.toNat = c.val + 256*d.val := by
    have hright : ((((d.bv.setWidth 16) <<< 8).setWidth 24)).toNat = 256*d.val := by
      rw [BitVec.toNat_setWidth_of_le (by decide),hds]
    simpa only [UScalar.bv_toNat] using or_low c.bv _ (by decide) d.val hright
  have hcds : (cd <<< 8).toNat = 256*(c.val+256*d.val) := by
    rw [shift_value _ (by rw [hcd]; change (c.val+256*d.val)*256<16777216; omega),hcd]
    omega
  let bcd : BitVec 32 := b.bv.setWidth 32 ||| ((cd <<< 8).setWidth 32)
  have hbcd : bcd.toNat = b.val + 256*(c.val+256*d.val) := by
    have hright : ((cd <<< 8).setWidth 32).toNat = 256*(c.val+256*d.val) := by
      rw [BitVec.toNat_setWidth_of_le (by decide),hcds]
    simpa only [UScalar.bv_toNat] using or_low b.bv _ (by decide) (c.val+256*d.val) hright
  have hbcds : (bcd <<< 8).toNat = 256*(b.val+256*(c.val+256*d.val)) := by
    rw [shift_value _ (by rw [hbcd]; change (b.val+256*(c.val+256*d.val))*256<4294967296; omega),hbcd]
    omega
  rw [PV_CB3_StagedByteShape.source]
  rw [← UScalar.bv_toNat (⟨PV_CB3_StagedByteShape.assembled a b c d⟩ : U32)]
  change (a.bv.setWidth 32 ||| (bcd <<< 8)).toNat = _
  simpa only [UScalar.bv_toNat] using or_low a.bv _ (by decide) (b.val+256*(c.val+256*d.val)) hbcds
#print axioms value
end R1Z.PV_CB3_StagedByteWord
