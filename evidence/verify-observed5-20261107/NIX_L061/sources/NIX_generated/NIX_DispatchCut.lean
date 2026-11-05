import NIX_Cuts
import NIX_PredecessorFrames
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIX_DispatchCut
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
abbrev Point := aspis_core.circle.SecureCirclePoint
abbrev Block := Array U8 32#usize
abbrev Reply := core.result.Result Block r1_wire.Error
abbrev Output := core.result.Result Point r1_wire.Error
structure Pre (Pointer : Type) where
 pointer : Pointer
 framed : Slice U8
 row : U8
 state : Block
 next : U8
 newState : Block
 newNext : U8
 reply : Reply
 point : Point
 count : Nat
 frame : Nat
 oldState : Block
 oldSample : Block
structure Post (Pointer : Type) where
 pointer : Option Pointer
 len : Nat
 row : U8
 state : Block
 next : U8
 at : Nat
 count : Nat
 sampleRow : FinishModel.CircleRow
 sampleBlock : Block
 frame : Nat
 transcriptState : Block
 transcriptNext : U8
 result : Output

def valid (row : U8) : Bool := row==25#u8 || row==26#u8

def childDomain : Reply → Prop
 | .Ok _=>True
 | .Err (.RowOrder _ _)=>True
 | _=>False

def expected {Pointer : Type} (s : Pre Pointer) : Output :=
 if valid s.row then match s.reply with | .Ok _=>.Ok s.point | .Err e=>.Err e
 else .Err .InvalidRow

/-- NIX_validated.rs.txt SHA256 f38a0198f0689a7e860f956df4067a135bfad96ff82ee716b1c47fbd79613d1f, K049/K050, instantiated by
NIX_validated_program with the actual SolanaDigest. Exact universal byte window
j<32: log row/ptr/len/next/pre-state/at; sample block and sample row on Ok;
transcript state/next, call count, cache frame on Err; all log cells and
transcript unchanged on invalid row; complete result and both RowOrder fields.
The 32-byte equality below is the universal j observation, not a new assertion.
Pre: len<=3717, count<254; reply is Ok or the explicit RowOrder constructor. -/
def cut {Pointer : Type} (s : Pre Pointer) (p : Post Pointer) : Prop :=
 s.framed.val.length≤3717 ∧ s.count<254 ∧ childDomain s.reply ∧ p.frame=s.frame ∧
 (if valid s.row then
  p.row=s.row ∧ p.pointer=some s.pointer ∧ p.len=s.framed.val.length ∧
  p.next=s.next ∧ p.state=s.state ∧ p.at=s.count ∧
  p.transcriptState=s.newState ∧ p.transcriptNext=s.newNext ∧
  (match s.reply with
   | .Ok block=>p.sampleBlock=block ∧
      p.sampleRow=(if s.row==25#u8 then .First else .Second) ∧ p.count=s.count+2
   | .Err _=>p.sampleBlock=s.oldSample ∧ p.sampleRow=.First ∧ p.count=s.count+1)
 else
  p.transcriptState=s.state ∧ p.transcriptNext=s.next ∧ p.count=s.count ∧
  p.sampleBlock=s.oldSample ∧ p.sampleRow=.First ∧ p.row=0#u8 ∧ p.pointer=none ∧
  p.len=0 ∧ p.state=s.oldState ∧ p.next=0#u8 ∧ p.at=0) ∧
 p.result=expected s

/-- All SAME predecessor records meet the concrete native borrowed-window bound. -/
theorem predecessor_domain (bytes : Slice U8) (pre : AspisR1PrefixAggregateParser.r1_wire.Prefix)
 (parsed : AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes=ok (.Ok pre)) (i : Fin 27) :
 (FJb_TailCell.cell pre.records i).val.length≤3717 := by
 rw [NIX_PredecessorFrames.aggregate bytes pre parsed i]
 exact (NGX_PrefixGeometry.widths i.val).2

/-- The two native branch tags are in the CLOSED block packet's row domain. -/
theorem row_domain (row : U8) (h : valid row=true) : row.val≤26 := by
 simp only [valid,Bool.or_eq_true,beq_iff_eq] at h
 rcases h with rfl|rfl <;> decide

/-- Error rejection is immediate and has no child/sampler suffix. -/
theorem invalid_result {Pointer : Type} (s : Pre Pointer) (p : Post Pointer)
 (certificate : cut s p) (invalid : valid s.row=false) : p.result=.Err .InvalidRow := by
 rw [certificate.2.2.2.2.2]
 simp only [expected,invalid,Bool.false_eq_true,if_false]

#print axioms predecessor_domain
#print axioms row_domain
#print axioms invalid_result
end AspisR1.NIX_DispatchCut
end
