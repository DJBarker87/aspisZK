import NJG_RowPrefixes
import NIX_CertificateFrames
set_option autoImplicit false
namespace AspisR1.NJG_ClaimsGeometry
open Aeneas Aeneas.Std Result AspisR1PublicPreparation

/-- Actual source allocation layouts agree: one MaybeUninit<Claims> versus
three initialized [QM31;29] rows. This arithmetic alone is not allocator-law
transport: reserve1/element1392 and reserve3/element464 still need their native
request/post/abort association to the adopted StdCalls instance. -/
theorem layouts : 1*(3*(29*16))=3*(29*16) ∧ 3*(29*16)=1392 := by decide

/-- Source decoder offsets are precisely0,29,58; no row is reused or skipped. -/
theorem offset (p : Fin 3) : 29*p.val+29≤87 ∧ 32*(29*p.val)+32*29≤3712 := by omega

/-- Every claims row uses the SAME row25 validated token; producer framing is
derived from the parsed predecessor, before allocation or decoder success. -/
theorem producer (bytes : Slice U8) (pre : AspisR1PrefixAggregateParser.r1_wire.Prefix)
 (parsed : AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes=ok (.Ok pre)) :
 ∃ record,r1_wire.Prefix.validated_record (PrefixAdapter.fromOld pre) 25#u8=ok (.Ok record) ∧
 record.row=25#u8 ∧ record.framed.val.length=3717 := by
 obtain ⟨record,call,tag,framed⟩:=NIX_ProducerInstall.framed bytes pre parsed 25#u8 (by decide)
 refine ⟨record,call,tag,?_⟩
 rw [framed]
 rfl

/-- Install decoder147's complete caller-domain packet for every source p.
No caller-success or chosen decoder-result premise appears. -/
theorem decoder (record : ClaimsUnrolledFinish.MainRecord) (p off : Usize)
 (live : p.val<3) (offset_eq : off.val=p.val*29) (row : record.row=25#u8)
 (framed : record.framed.val.length=3717) :
 record.framed.val.length≤3717 ∧
 32*off.val+32*29≤record.framed.val.length-5 ∧
 ∃ reply,AspisS1ExtractedRoundChildren.decodeMain 29#usize record off=ok reply := by
 have h:record.row.val=25:=by rw [row];rfl
 have g:record.framed.val.length=NGX_PrefixGeometry.width 25:=by rw [framed];rfl
 exact NIH_DecodeInstall.claims record p off h live offset_eq g

theorem source_offset (p : Usize) (live : p.val<3) :
 ∃ off,p*29#usize=ok off ∧ off.val=p.val*29 := by
 obtain ⟨off,run,value⟩:=WP.spec_imp_exists (UScalar.mul_spec (x:=p) (y:=29#usize) (by scalar_tac))
 exact ⟨off,run,by simpa only [show (29#usize).val=29 from rfl] using value⟩

#print axioms layouts
#print axioms offset
#print axioms producer
#print axioms decoder
#print axioms source_offset
end AspisR1.NJG_ClaimsGeometry
