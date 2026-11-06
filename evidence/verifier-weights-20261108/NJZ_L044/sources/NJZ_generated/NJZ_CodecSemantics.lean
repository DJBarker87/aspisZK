import NJZ_CodecProjection
set_option autoImplicit false
noncomputable section
namespace NJZ_CodecSemantics
open NFU_Retarget
open Aeneas Aeneas.Std Result AspisR1
open OraclePortCkptAbi4Decode CheckpointBytes3EShape CheckpointBytes3ScalarShape
attribute [local instance] Classical.propDecidable

def zero : AspisR1Stage2.aspis_core.field.QM31 := ⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩

theorem canonical_shape (w : Fin 8 → U32) :
 CanonicalWide (eWords w) ↔ NJZ_Echeck.Canonical (fun i=>(w i).val) := by
 simp [CanonicalWide,Canonical,eWords,kWords,NJZ_Echeck.Canonical,Fin.forall_fin_succ]

theorem high_four (w : NJZ_Echeck.Words) :
 NJZ_Echeck.HighZero w ↔ w 4=0 ∧ w 5=0 ∧ w 6=0 ∧ w 7=0 := by
 constructor
 · intro h;exact ⟨h 4 (by decide),h 5 (by decide),h 6 (by decide),h 7 (by decide)⟩
 · rintro ⟨h4,h5,h6,h7⟩ i hi
   fin_cases i <;> simp_all

theorem high_shape (w : Fin 8 → U32) :
 (CheckpointBytes3Namespaces.fromE (eWords w)).c1=zero ↔
 NJZ_Echeck.HighZero (fun i=>(w i).val) := by
 rw [high_four]
 constructor
 · intro h
   exact ⟨by simpa [CheckpointBytes3Namespaces.fromE,CheckpointBytes3Namespaces.fromK,eWords,kWords,zero]
                using congrArg (fun q : AspisR1Stage2.aspis_core.field.QM31=>q.c0.a.val) h,
          by simpa [CheckpointBytes3Namespaces.fromE,CheckpointBytes3Namespaces.fromK,eWords,kWords,zero]
                using congrArg (fun q : AspisR1Stage2.aspis_core.field.QM31=>q.c0.b.val) h,
          by simpa [CheckpointBytes3Namespaces.fromE,CheckpointBytes3Namespaces.fromK,eWords,kWords,zero]
                using congrArg (fun q : AspisR1Stage2.aspis_core.field.QM31=>q.c1.a.val) h,
          by simpa [CheckpointBytes3Namespaces.fromE,CheckpointBytes3Namespaces.fromK,eWords,kWords,zero]
                using congrArg (fun q : AspisR1Stage2.aspis_core.field.QM31=>q.c1.b.val) h⟩
 · rintro ⟨h4,h5,h6,h7⟩
   have a : w 4=0#u32:=UScalar.eq_of_val_eq h4
   have b : w 5=0#u32:=UScalar.eq_of_val_eq h5
   have c : w 6=0#u32:=UScalar.eq_of_val_eq h6
   have d : w 7=0#u32:=UScalar.eq_of_val_eq h7
   simp only [CheckpointBytes3Namespaces.fromE,CheckpointBytes3Namespaces.fromK,eWords,kWords,zero,a,b,c,d]

def parsedStep (b : Array U8 32#usize) (k : Bool) : Bool :=
 match NJC_EReaderResults.naturalE b with
 | .Err _ => false
 | .Ok q => !k || decide (q.c1=zero)

/-- CLOSED decoder guard and full decoded high limbs imply exactly the source
one-iteration verdict on these SAME32bytes, including canonical rejection. -/
theorem source (b : Array U8 32#usize) (k : Bool) :
 parsedStep b k=LPl.Echeck.chunk b.val k := by
 have word_eq : (fun i=>(CheckpointBytes3EDecode.word32 b.to_slice b.property i).val)=
   NJZ_Echeck.words b.val := funext (NJZ_CodecProjection.word b)
 have can := canonical_shape (CheckpointBytes3EDecode.word32 b.to_slice b.property)
 have high := high_shape (CheckpointBytes3EDecode.word32 b.to_slice b.property)
 rw [word_eq] at can high
 rw [←NJZ_Echeck.step_chunk]
 unfold parsedStep NJC_EReaderResults.naturalE NJZ_Echeck.decode NJZ_Echeck.step
 by_cases h : NJZ_Echeck.Canonical (NJZ_Echeck.words b.val)
 · rw [if_pos h,if_pos (can.mpr h)]
   change (!k || decide ((CheckpointBytes3Namespaces.fromE
     (eWords (CheckpointBytes3EDecode.word32 b.to_slice b.property))).c1=zero))=
     (!k || decide (NJZ_Echeck.HighZero (NJZ_Echeck.words b.val)))
   rw [high]
 · rw [if_neg h,if_neg (fun hc=>h (can.mp hc))]

/-- The returned child payload meets the one-step native canonical domain;
canonicality is derived from decoding, never added to the outer caller. -/
def ReplyDomain : core.result.Result AspisR1Stage2.aspis_core.field.wide_exact.WideExact
 AspisR1Stage2.verifier.Error → Prop
 | .Err _ => True
 | .Ok q => CanonicalWide (CheckpointBytes3Namespaces.toE q)

theorem domain (b : Array U8 32#usize) : ReplyDomain (NJC_EReaderResults.naturalE b) := by
 change ReplyDomain (if CanonicalWide
   (eWords (CheckpointBytes3EDecode.word32 b.to_slice b.property)) then
    core.result.Result.Ok (CheckpointBytes3Namespaces.fromE
     (eWords (CheckpointBytes3EDecode.word32 b.to_slice b.property)))
   else core.result.Result.Err AspisR1Stage2.verifier.Error.Checkpoint)
 by_cases h : CanonicalWide (eWords (CheckpointBytes3EDecode.word32 b.to_slice b.property))
 · rw [if_pos h]
   simpa only [ReplyDomain,CheckpointBytes3Namespaces.to_from_e] using h
 · rw [if_neg h]
   trivial

/-- Instantiated Bool projection of the exact local Option<E>/Result contract.
The native full payload/call-count/byte frame is recorded separately. -/
def replyStep (reply : Option AspisR1Stage2.aspis_core.field.wide_exact.WideExact)
 (k : Bool) : Bool := match reply with
 | none => false
 | some q => !k || decide (q.c1=zero)

def NativeCut (reply : Option AspisR1Stage2.aspis_core.field.wide_exact.WideExact)
 (k out : Bool) : Prop := out=replyStep reply k

def decoded (b : Array U8 32#usize) := match NJC_EReaderResults.naturalE b with
 | .Err _ => none | .Ok q => some q

/-- This is the (y)(3) instantiation of NativeCut with the CLOSED parser's
complete reply, not a new native assertion about an uninterpreted oracle. -/
def Cut (b : Array U8 32#usize) (k out : Bool) : Prop := NativeCut (decoded b) k out

theorem cut_projection (b : Array U8 32#usize) (k out : Bool) (cut : Cut b k out) :
 out=parsedStep b k := by
 unfold Cut NativeCut decoded replyStep at cut
 cases h : NJC_EReaderResults.naturalE b <;> simpa only [parsedStep,h] using cut

/-- Full positive root after child substitution: each window is supplied by
its reviewed source-step cut and concrete ChunksExact frame. No accepted-run,
trace, parent result or child-success premise is used. -/
theorem root (bs : Slice U8) (k : Bool) (replies : Nat → Bool)
 (cuts : ∀ i,i<bs.val.length/32→∃ b : Array U8 32#usize,
  b.val=(bs.val.drop (32*i)).take 32 ∧ Cut b k (replies i)) :
 NFU_Retarget.verifier.echeck bs k=
 ok (if (List.range (bs.val.length/32)).all replies then .Ok () else .Err .Parse) := by
 apply NJZ_Echeck.root bs k replies
 intro i hi
 obtain ⟨b,window,cut⟩:=cuts i hi
 change replies i=NJZ_Echeck.step (NJZ_Echeck.decode
   (NJZ_Echeck.words ((bs.val.drop (32*i)).take 32))) k
 rw [NJZ_Echeck.step_chunk,←window]
 exact (cut_projection b k (replies i) cut).trans (source b k)

#print axioms canonical_shape
#print axioms high_four
#print axioms high_shape
#print axioms source
#print axioms domain
#print axioms cut_projection
#print root
#print axioms root
end NJZ_CodecSemantics
