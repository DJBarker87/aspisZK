import NIX_ProducerInstall
set_option autoImplicit false
namespace AspisR1.NJG_RoundProducer
open Aeneas Aeneas.Std Result AspisR1PublicPreparation

def row (r : Usize) (bound : r.val<10) : U8 :=
 U8.ofNat (15+r.val) (by scalar_tac)

theorem row_value (r : Usize) (bound : r.val<10) :
 (row r bound).val=15+r.val := rfl

theorem row_add (r : Usize) (bound : r.val<10) :
 15#u8 + UScalar.cast .U8 r=ok (row r bound) := by
 have cv : (UScalar.cast .U8 r).val=r.val := by scalar_tac
 obtain ⟨v,run,hv⟩:=WP.spec_imp_exists (UScalar.add_spec (x:=15#u8) (y:=UScalar.cast .U8 r) (by scalar_tac))
 have same : v=row r bound := by scalar_tac
 simpa only [same] using run

theorem same_record (pre : AspisR1PrefixAggregateParser.r1_wire.Prefix)
 (r : Usize) (bound : r.val<10) :
 ∃ record,r1_wire.Prefix.validated_record (PrefixAdapter.fromOld pre) (row r bound)=ok (.Ok record) ∧
 record.row=row r bound ∧ record.framed=FJb_TailCell.cell pre.records
  ⟨15+r.val,by change 15+r.val<27;omega⟩ := by
 simpa only [row_value] using NIX_ProducerInstall.lookup pre (row r bound) (by rw [row_value];omega)

/-- Producer domain is derived before decoder, boundary, semantic or finish
success. This is the SAME parser/token used by both native getter sites. -/
theorem framed (bytes : Slice U8) (pre : AspisR1PrefixAggregateParser.r1_wire.Prefix)
 (parsed : AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes=ok (.Ok pre))
 (r : Usize) (bound : r.val<10) :
 ∃ record,r1_wire.Prefix.validated_record (PrefixAdapter.fromOld pre) (row r bound)=ok (.Ok record) ∧
 record.row=row r bound ∧ record.framed.val.length=901 := by
 obtain ⟨record,run,tag,width⟩:=NIX_ProducerInstall.framed bytes pre parsed (row r bound)
  (by rw [row_value];omega)
 refine ⟨record,run,tag,?_⟩
 rw [width]
 have low : 15≤(row r bound).val:=by rw [row_value];omega
 have high : (row r bound).val≤24:=by rw [row_value];omega
 unfold NGX_PrefixGeometry.width NFU_PacketDomains.payloadSize
 split_ifs <;> omega

#print axioms row_value
#print axioms row_add
#print axioms same_record
#print axioms framed
end AspisR1.NJG_RoundProducer
