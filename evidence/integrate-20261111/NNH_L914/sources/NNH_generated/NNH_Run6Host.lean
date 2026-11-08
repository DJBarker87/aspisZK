import NNH_Run6Fields
import NNH_Run6NMF
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_Run6Host
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open NNH_Libraries
variable {W Tx : Type}
 (L0 : Library W (Nat → Record))
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy)
abbrev S := NNH_Run5bHost.S_host (Tx := Tx) L0 copy std
abbrev R := NNH_Run5bExec.recSig (Tx := Tx) L0 copy std
abbrev X := NNH_Run5bExec.exec (Tx := Tx) L0 copy std
abbrev RestLaw := ∀ c n1 n2, (S L0 copy std).Extraction c n1 n2 →
 (S L0 copy std).Accepted1 c n1 → (S L0 copy std).Game c n1 n2 →
 (S L0 copy std).Queries c n1 → NNH_Run5bSplit.rest L0 copy c n1 n2

def split (rest : RestLaw (Tx := Tx) L0 copy std) : RSL.TFM.Split (S (Tx := Tx) L0 copy std) where
 Rest := NNH_Run5bSplit.rest L0 copy
 Outcome := NNH_Run5bSplit.outcome L0 copy
 concl_iff := NNH_Run5bSplit.conclusion_iff L0 copy
 rest := rest

theorem sig_same : NNH_G1aEnv.sig (S (Tx := Tx) L0 copy std) = S (Tx := Tx) L0 copy std := rfl

def g1a (I : RSL.TAS.Impl L V0 VL) : RSL.NNT.NNC_G1aL (S (Tx := Tx) L0 copy std) L V0 VL I :=
 NNT_G1aLaw.field (S (Tx := Tx) L0 copy std) I

def nmfB (I : RSL.TAS.Impl L V0 VL) :
 NNT_TopL.NNC_NMFPrimeB (S (Tx := Tx) L0 copy std) L D V0 VL P C I
  (g1a L0 copy std I) (R L0 copy std) := NNH_Run6NMF.nmfB L0 copy std I

example (I : RSL.TAS.Impl L V0 VL) : (g1a (Tx := Tx) L0 copy std I).w = V0.tx2auth := rfl
example : (X (Tx := Tx) L0 copy std).exhibited_mk = (fun _ _ _ _ _ => rfl) := rfl
#print axioms split
#print axioms sig_same
#print axioms g1a
#print axioms nmfB
end AspisR1.NNH_Run6Host
end
