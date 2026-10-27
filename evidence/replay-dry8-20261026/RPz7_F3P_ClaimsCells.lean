import RPz7_F3P_ThreeRows
import RPz7_F3P_DecodeCircleIndex
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3P_ClaimsCells
open Aeneas Aeneas.Std Result AspisR1PublicPreparation

theorem cells (r : r1_wire.ValidatedRecord) (a b c : Array aspis_core.field.QM31 29#usize)
    (d0 : AspisS1ExtractedRoundChildren.decodeMain 29#usize r 0#usize=ok (.Ok a))
    (d1 : AspisS1ExtractedRoundChildren.decodeMain 29#usize r 29#usize=ok (.Ok b))
    (d2 : AspisS1ExtractedRoundChildren.decodeMain 29#usize r 58#usize=ok (.Ok c))
    (values : CircleRecordCodec.Payload 0)
    (decoded : CircleRecordCodec.decode 0 (MultiproofConeCanonical.bytesOf r.framed.val)=some values)
    (point l : Usize) (hp : point.val<3) (hl : l.val<29)
    (row : Array aspis_core.field.QM31 29#usize) (scalar : aspis_core.field.QM31)
    (readRow : Array.index_usize (Array.make 3#usize [a,b,c]) point=ok row)
    (read : Array.index_usize row l=ok scalar) :
    LiteralOpeningView.eK (F3L_RhoMeaning.decode scalar)=
      (values ⟨29*point.val+l.val,by change 29*point.val+l.val<116;omega⟩).val := by
  rcases F3P_ThreeRows.selected a b c point hp row readRow with ⟨p0,r0⟩|⟨p1,r1⟩|⟨p2,r2⟩
  · subst row
    have numeric := F3P_DecodeCircleIndex.cell r 0#usize a d0 0 values decoded l hl (by change 0+l.val<116;omega) scalar read
    apply numeric.trans
    apply congrArg (fun j=>(values j).val)
    apply Fin.ext
    change 0+l.val=29*point.val+l.val
    omega
  · subst row
    have numeric := F3P_DecodeCircleIndex.cell r 29#usize b d1 0 values decoded l hl (by change 29+l.val<116;omega) scalar read
    apply numeric.trans
    apply congrArg (fun j=>(values j).val)
    apply Fin.ext
    change 29+l.val=29*point.val+l.val
    omega
  · subst row
    have numeric := F3P_DecodeCircleIndex.cell r 58#usize c d2 0 values decoded l hl (by change 58+l.val<116;omega) scalar read
    apply numeric.trans
    apply congrArg (fun j=>(values j).val)
    apply Fin.ext
    change 58+l.val=29*point.val+l.val
    omega

#print axioms cells
end AspisR1.F3P_ClaimsCells
end
