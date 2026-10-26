import BEf_Carrier
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEf_Pure
open Aeneas Aeneas.Std Result SdkC_Source

def call {S : Type} (hashv : Parts → Result Digest) (parts : Parts) (state : S) :=
  (hashv parts,state)

/-- Full state/log/Result, including outer failures and divergence, for a
frame-preserving read interpreter. No successful-run premise. -/
theorem exact {S A : Type} (hashv : Parts → Result Digest) (code : Code A)
    (state : S) (before : Log) :
    BEf_Carrier.run (call hashv) code state before =
      ((SdkC_Source.run hashv code before).1,state,(SdkC_Source.run hashv code before).2) := by
  have projected := BEf_Carrier.source (call hashv) hashv (fun _ _ => rfl) code state before
  have framed := BEf_Carrier.frame (call hashv) (fun _ _ => rfl) code state before
  apply Prod.ext
  · exact congrArg Prod.fst projected
  · apply Prod.ext framed
    exact congrArg Prod.snd projected

theorem prefix {S A : Type} (hashv : Parts → Result Digest) (code : Code A)
    (state : S) (before : Log) :
    ∃ suffix, (BEf_Carrier.run (call hashv) code state before).2.2 = before ++ suffix := by
  rw [exact]
  exact SdkC_Source.prefix_preserved hashv code before

theorem associated {S A : Type} (hashv : Parts → Result Digest) (code : Code A)
    (state : S) (before : Log)
    (initial : ∀ q ∈ before, q.returned = hashv q.parts) :
    ∀ q ∈ (BEf_Carrier.run (call hashv) code state before).2.2,
      q.returned = hashv q.parts := by
  rw [exact]
  exact SdkC_Source.associated hashv code before initial

#print axioms exact
#print axioms prefix
#print axioms associated
end AspisR1.BEf_Pure
end
