import FJl_TailWindow0
import FJl_TailWindow1
import FJl_TailWindow2
import FJl_C1Coordinates
import FJl_C2Coordinates
import FJl_WindowArithmetic
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJl_TailLiteral
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open FIo_FieldBridge (NQ qm)
open MultiproofConeCanonical
/-- VALUE at the actual C1 tail read, identical literal byte window. -/
theorem c1 (q : Array U8 608#usize) (c : MixedLeafEncoding.C1)
    (decoded : MixedLeafDecoder.decodeC1 ((bytesOf q.val).take 480)=some c)
    (s : Fin 4) (slot : Usize) (same : slot.val=s.val) (v : NQ)
    (run : FJi_TailInputs.read0 q slot=ok v) : decodeQM (qm v)=(c s).2 := by
  have h := FJl_TailWindow0.value q slot (by rw [same];exact s.isLt) v run
  have literal := FJl_C1Coordinates.tail _ c decoded s
  rw [FJl_WindowArithmetic.c1tail _ _ s.isLt] at literal
  change ExactLeafFieldCodec.decodeQM31
    (OraclePortCompactDraft.slice (bytesOf q.val) (120*s.val+104) 16)=some ((c s).2) at literal
  rw [same,literal] at h
  exact (Option.some.inj h).symm

/-- VALUE at the first C2 coordinate, identical literal byte window. -/
theorem c2first (q : Array U8 608#usize) (c : MixedLeafEncoding.C2)
    (decoded : MixedLeafDecoder.decodeC2 (((bytesOf q.val).drop 480).take 128)=some c)
    (s : Fin 4) (slot : Usize) (same : slot.val=s.val) (v : NQ)
    (run : FJi_TailInputs.read1 q slot=ok v) : decodeQM (qm v)=c s 0 := by
  have h := FJl_TailWindow1.value q slot (by rw [same];exact s.isLt) v run
  have literal := FJl_C2Coordinates.coordinate _ c decoded s (0 : Fin 2)
  rw [FJl_WindowArithmetic.c2 _ _ _ s.isLt (by decide)] at literal
  have l0 : (0 : Fin 2).val=0 := by decide
  simp only [l0,Nat.mul_zero,Nat.add_zero] at literal
  change ExactLeafFieldCodec.decodeQM31
    (OraclePortCompactDraft.slice (bytesOf q.val) (480+32*s.val) 16)=some (c s 0) at literal
  rw [same,literal] at h
  exact (Option.some.inj h).symm

/-- VALUE at the second C2 coordinate, identical literal byte window. -/
theorem c2second (q : Array U8 608#usize) (c : MixedLeafEncoding.C2)
    (decoded : MixedLeafDecoder.decodeC2 (((bytesOf q.val).drop 480).take 128)=some c)
    (s : Fin 4) (slot : Usize) (same : slot.val=s.val) (v : NQ)
    (run : FJi_TailInputs.read2 q slot=ok v) : decodeQM (qm v)=c s 1 := by
  have h := FJl_TailWindow2.value q slot (by rw [same];exact s.isLt) v run
  have literal := FJl_C2Coordinates.coordinate _ c decoded s (1 : Fin 2)
  rw [FJl_WindowArithmetic.c2 _ _ _ s.isLt (by decide)] at literal
  have l1 : (1 : Fin 2).val=1 := by decide
  simp only [l1,Nat.mul_one] at literal
  change ExactLeafFieldCodec.decodeQM31
    (OraclePortCompactDraft.slice (bytesOf q.val) (480+32*s.val+16) 16)=some (c s 1) at literal
  rw [same,literal] at h
  exact (Option.some.inj h).symm
#print axioms c1
#print axioms c2first
#print axioms c2second
end AspisR1.FJl_TailLiteral
end
