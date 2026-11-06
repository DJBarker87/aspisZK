import NJZ_CodecProjection
set_option autoImplicit false
noncomputable section
namespace NJZ_CodecSemantics
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
 parsedStep b k=LPt_LPl.Echeck.chunk b.val k := by
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

#print axioms canonical_shape
#print axioms high_four
#print axioms high_shape
#print axioms source
end NJZ_CodecSemantics
