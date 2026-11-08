import NNH_Run5bHost
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_Run5bAcceptance
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open NNH_Run5bHost NNH_Libraries
variable {W Tx : Type} (L0 : Library W (Nat → Record))
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy)

def a3 : RSL.TAS.NNE_A3 (S_host (Tx := Tx) L0 copy std) VL P C :=
 NNH_RecordSig.a3 (envSig L0 copy) (data L0 copy std) (record L0 copy) VL P C

def a4 : RSL.TAS.NNE_A4 (S_host (Tx := Tx) L0 copy std) L D V0 :=
 NNH_RecordSig.a4 (envSig L0 copy) (data L0 copy std) (record L0 copy) L D V0

def a5 (I : RSL.TAS.Impl L V0 VL) :
 RSL.TAS.NNE_A5 (S_host (Tx := Tx) L0 copy std) L V0 VL P C I where
 recorded := by
  intro c a1 hx h1 g2 reject trace
  have h := (NNH_RecordSig.a5 (envSig L0 copy) (data L0 copy std)
   (record L0 copy) L V0 VL P C I).recorded
  exact h c a1 hx h1 g2 reject trace
#print axioms a3
#print axioms a4
#print axioms a5
end AspisR1.NNH_Run5bAcceptance
end
