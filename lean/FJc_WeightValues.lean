import FJc_WeightQMMul
import FIo_QMMulValues
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJc_WeightValues
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open FJc_WeightQMBridge (SQ)
open FIo_Install (toQ)
def Canon (x : SQ) : Prop := FIo_QMValues.Canon (toQ x)
def decode (x : SQ) : OraclePortCheckpointAbiC5.K := decodeQM (FIo_FieldBridge.qm (toQ x))

theorem add (x y z : SQ) (hx : Canon x) (hy : Canon y)
    (run : FIn_WeightsExtract.field.QM31.add x y=ok z) :
    Canon z ∧ decode z=decode x+decode y :=
  FIo_QMValues.add _ _ _ hx hy (FJc_WeightQMBridge.add x y z run)

theorem sub (x y z : SQ) (hx : Canon x) (hy : Canon y)
    (run : FIn_WeightsExtract.field.QM31.sub x y=ok z) :
    Canon z ∧ decode z=decode x-decode y :=
  FIo_QMValues.sub _ _ _ hx hy (FJc_WeightQMBridge.sub x y z run)

theorem mul (x y z : SQ) (hx : Canon x) (hy : Canon y)
    (run : FIn_WeightsExtract.field.QM31.mul x y=ok z) :
    Canon z ∧ decode z=decode x*decode y :=
  FIo_QMMulValues.mul _ _ _ hx hy (FJc_WeightQMMul.mul x y z run)
#print axioms add
#print axioms sub
#print axioms mul
end AspisR1.FJc_WeightValues
end
