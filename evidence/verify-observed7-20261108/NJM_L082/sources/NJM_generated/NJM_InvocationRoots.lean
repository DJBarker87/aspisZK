import NJM_RoundsClosed
import NJM_CircleInvalid
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJM_InvocationRoots
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NIX_CertificateFrames NJG_RoundsCode
abbrev Q := aspis_core.field.QM31

def index (r : Fin 10) : Usize := Usize.ofNat r.val (by have h:=r.isLt;scalar_tac)
def row (r : Fin 27) : U8 := U8.ofNat r.val (by have h:=r.isLt;change r.val≤255;omega)

/-- Actual caller constructor case, rather than an assumed parse-success
premise. Rejected parses never enter133. Every entered clause is discharged by
the concrete source/cut packet; the actual private caller's ten sites supply
this finite index domain. -/
theorem round {H : Type} (D : aspis_core.Digest32 H) (bytes : Slice U8)
 (before : r1_wire.SemanticTranscript H) (a : Alpha) (running : Q) (r : Fin 10) :
 match parsed : AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes with
 | .ok (.Ok pre)=>NJM_RoundsClosed.Child D bytes pre parsed before a running (index r)
    (by change r.val<10;exact r.isLt)
 | .ok (.Err _) => True
 | .fail _ => True
 | .div => True := by
 split
 · rename_i pre parsed
   exact NJM_RoundJoined.source D bytes pre parsed before a running (index r) (by change r.val<10;exact r.isLt)
 · trivial
 · trivial
 · trivial

/-- Full134 statement at the actual constructor arm, with no parse-success,
child-output, endpoint, Run or operation-dictionary hypothesis. The only Prop
parameter is the reviewed native K016–019 cut. -/
theorem rounds {H : Type} (native : NJM_RoundsCut.Observations) (cut : NJM_RoundsCut.Cut native)
 (token frame : Nat) (D : aspis_core.Digest32 H) (bytes : Slice U8)
 (t : r1_wire.SemanticTranscript H) :
 match parsed : AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes with
 | .ok (.Ok pre)=>
   (∃ running,PreparedHashCode.run (S1SemanticCode.rounds NJM_RoundJoin.R D (PrefixAdapter.fromOld pre) t)=
    NJM_RoundsInduction.chain native token frame D (PrefixAdapter.fromOld pre) sites
     (running,Array.repeat 10#usize aspis_core.field.QM31.ZERO,t)) ∧
   (∀ (r : Usize) (member : r∈sites) (carry : Carry H),
    NJM_RoundsClosed.Child D bytes pre parsed carry.2.2 carry.2.1 carry.1 r (NJG_RoundsCode.sites_domain r member))
 | .ok (.Err _) => True
 | .fail _ => True
 | .div => True := by
 split
 · rename_i pre parsed
   exact NJM_RoundsClosed.source native cut token frame D bytes pre parsed t
 · trivial
 · trivial
 · trivial

/-- Complete concrete142 per-record packet, including invalid native cuts.
This predicate contains no assumed child law and is PROVED by circle below. -/
def Circle {Pointer H : Type} (D : aspis_core.Digest32 H) (template : NIX_DispatchCut.Pre Pointer)
 (before : r1_wire.SemanticTranscript H) (record : r1_wire.ValidatedRecord) : Prop :=
 record.framed.val.length≤3717 ∧
 (record.row=25#u8 → NJM_CircleRoot.Branch D template before record .First) ∧
 (record.row=26#u8 → NJM_CircleRoot.Branch D template before record .Second) ∧
 (record.row≠25#u8 → record.row≠26#u8 →
  ∀ post,NIX_DispatchCut.cut (NJM_CircleNative.install (NJM_CircleInvalid.inputs template record before)) post →
  PreparedHashCode.run (NJM_CircleCode.source D before record)=([],ok (post.result,before)) ∧
  post.transcriptState=before.state ∧ post.transcriptNext=before.next_row ∧ post.count=0 ∧ post.frame=template.frame)

/-- Actual SAME parser/getter supplies the record and its size bound. Neither
parse/getter success nor a record payload, point value, dictionary or endpoint
is an external hypothesis. All27 source records cover both circle tags and
all invalid-tag branches of this private caller interface. -/
theorem circle {Pointer H : Type} (D : aspis_core.Digest32 H) (template : NIX_DispatchCut.Pre Pointer)
 (bytes : Slice U8) (before : r1_wire.SemanticTranscript H) (slot : Fin 27) :
 match parsed : AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes with
 | .ok (.Ok pre)=>
   ∃ record,r1_wire.Prefix.validated_record (PrefixAdapter.fromOld pre) (row slot)=ok (.Ok record) ∧
    record.row=row slot ∧ Circle D template before record
 | .ok (.Err _) => True
 | .fail _ => True
 | .div => True := by
 split
 · rename_i pre parsed
   obtain ⟨record,getter,tag,geometry⟩:=NIX_ProducerInstall.framed bytes pre parsed (row slot) (by change slot.val<27;exact slot.isLt)
   have bound : record.framed.val.length≤3717 := by
    rw [geometry]
    exact (NGX_PrefixGeometry.widths (row slot).val).2
   have valid:=NJM_CircleRoot.source D template before record bound
   refine ⟨record,getter,tag,bound,valid.1,valid.2.1,?_⟩
   intro notFirst notSecond post certificate
   exact NJM_CircleInvalid.source D template record before notFirst notSecond post certificate
 · trivial
 · trivial
 · trivial

#print axioms round
#print axioms rounds
#print axioms circle
end AspisR1.NJM_InvocationRoots
end
