import PV_B3P_InitializerEvents578227
namespace PV_B3P_InitializerFamily578227
open Aeneas Aeneas.Std PV_B3P_PanicPatterns571227 PV_B3P_InitializerEvents578227
set_option autoImplicit false
/-- Actual LLBC instance 370:ce8f37c13c92e9e52a4a, source instruction 24928. -/
def sourceState_0_24928 {α β γ : Type} (count length : Usize)
    (effects : Effects α β γ) : Result (Option IndexState) := sourceEvent .indexPrecondition count length effects
theorem certificate_0_24928 {α β γ δ : Type} (count length : Usize)
    (effects : Effects α β γ) (observed : IndexState)
    (ran : sourceState_0_24928 count length effects = .ok (some observed))
    (normal first second : Result δ) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_index_certificate .indexPrecondition count length effects observed ran normal first second
#print axioms certificate_0_24928
/-- Actual LLBC instance 370:ce8f37c13c92e9e52a4a, source instruction 30822. -/
def sourceState_0_30822 {α β γ : Type} (count length : Usize)
    (effects : Effects α β γ) : Result (Option IndexState) := sourceEvent .index count length effects
theorem certificate_0_30822 {α β γ δ : Type} (count length : Usize)
    (effects : Effects α β γ) (observed : IndexState)
    (ran : sourceState_0_30822 count length effects = .ok (some observed))
    (normal first second : Result δ) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_index_certificate .index count length effects observed ran normal first second
#print axioms certificate_0_30822
/-- Actual LLBC instance 370:ce8f37c13c92e9e52a4a, source instruction 24973. -/
def sourceState_0_24973 {α β γ : Type} (count length : Usize)
    (effects : Effects α β γ) : Result (Option IndexState) := sourceEvent .addPrecondition count length effects
theorem certificate_0_24973 {α β γ δ : Type} (count length : Usize)
    (effects : Effects α β γ) (observed : IndexState)
    (ran : sourceState_0_24973 count length effects = .ok (some observed))
    (normal first second : Result δ) :
    ¬ diagnostic (arithmeticGuard (.add observed.index 1 (UScalar.max .Usize))) ∧
      branch (arithmeticGuard (.add observed.index 1 (UScalar.max .Usize))) normal first = branch (arithmeticGuard (.add observed.index 1 (UScalar.max .Usize))) normal second :=
  event_add_certificate count length effects observed ran normal first second
#print axioms certificate_0_24973
/-- Actual LLBC instance 370:690f121ef3ceb4c7859a, source instruction 24928. -/
def sourceState_1_24928 {α β γ : Type} (count length : Usize)
    (effects : Effects α β γ) : Result (Option IndexState) := sourceEvent .indexPrecondition count length effects
theorem certificate_1_24928 {α β γ δ : Type} (count length : Usize)
    (effects : Effects α β γ) (observed : IndexState)
    (ran : sourceState_1_24928 count length effects = .ok (some observed))
    (normal first second : Result δ) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_index_certificate .indexPrecondition count length effects observed ran normal first second
#print axioms certificate_1_24928
/-- Actual LLBC instance 370:690f121ef3ceb4c7859a, source instruction 30822. -/
def sourceState_1_30822 {α β γ : Type} (count length : Usize)
    (effects : Effects α β γ) : Result (Option IndexState) := sourceEvent .index count length effects
theorem certificate_1_30822 {α β γ δ : Type} (count length : Usize)
    (effects : Effects α β γ) (observed : IndexState)
    (ran : sourceState_1_30822 count length effects = .ok (some observed))
    (normal first second : Result δ) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_index_certificate .index count length effects observed ran normal first second
#print axioms certificate_1_30822
/-- Actual LLBC instance 370:690f121ef3ceb4c7859a, source instruction 24973. -/
def sourceState_1_24973 {α β γ : Type} (count length : Usize)
    (effects : Effects α β γ) : Result (Option IndexState) := sourceEvent .addPrecondition count length effects
theorem certificate_1_24973 {α β γ δ : Type} (count length : Usize)
    (effects : Effects α β γ) (observed : IndexState)
    (ran : sourceState_1_24973 count length effects = .ok (some observed))
    (normal first second : Result δ) :
    ¬ diagnostic (arithmeticGuard (.add observed.index 1 (UScalar.max .Usize))) ∧
      branch (arithmeticGuard (.add observed.index 1 (UScalar.max .Usize))) normal first = branch (arithmeticGuard (.add observed.index 1 (UScalar.max .Usize))) normal second :=
  event_add_certificate count length effects observed ran normal first second
#print axioms certificate_1_24973
/-- Actual LLBC instance 370:bd9f80896880a57a5801, source instruction 24928. -/
def sourceState_2_24928 {α β γ : Type} (count length : Usize)
    (effects : Effects α β γ) : Result (Option IndexState) := sourceEvent .indexPrecondition count length effects
theorem certificate_2_24928 {α β γ δ : Type} (count length : Usize)
    (effects : Effects α β γ) (observed : IndexState)
    (ran : sourceState_2_24928 count length effects = .ok (some observed))
    (normal first second : Result δ) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_index_certificate .indexPrecondition count length effects observed ran normal first second
#print axioms certificate_2_24928
/-- Actual LLBC instance 370:bd9f80896880a57a5801, source instruction 30822. -/
def sourceState_2_30822 {α β γ : Type} (count length : Usize)
    (effects : Effects α β γ) : Result (Option IndexState) := sourceEvent .index count length effects
theorem certificate_2_30822 {α β γ δ : Type} (count length : Usize)
    (effects : Effects α β γ) (observed : IndexState)
    (ran : sourceState_2_30822 count length effects = .ok (some observed))
    (normal first second : Result δ) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_index_certificate .index count length effects observed ran normal first second
#print axioms certificate_2_30822
/-- Actual LLBC instance 370:bd9f80896880a57a5801, source instruction 24973. -/
def sourceState_2_24973 {α β γ : Type} (count length : Usize)
    (effects : Effects α β γ) : Result (Option IndexState) := sourceEvent .addPrecondition count length effects
theorem certificate_2_24973 {α β γ δ : Type} (count length : Usize)
    (effects : Effects α β γ) (observed : IndexState)
    (ran : sourceState_2_24973 count length effects = .ok (some observed))
    (normal first second : Result δ) :
    ¬ diagnostic (arithmeticGuard (.add observed.index 1 (UScalar.max .Usize))) ∧
      branch (arithmeticGuard (.add observed.index 1 (UScalar.max .Usize))) normal first = branch (arithmeticGuard (.add observed.index 1 (UScalar.max .Usize))) normal second :=
  event_add_certificate count length effects observed ran normal first second
#print axioms certificate_2_24973
/-- Actual LLBC instance 370:e926d80d1d048ac77607, source instruction 24928. -/
def sourceState_3_24928 {α β γ : Type} (count length : Usize)
    (effects : Effects α β γ) : Result (Option IndexState) := sourceEvent .indexPrecondition count length effects
theorem certificate_3_24928 {α β γ δ : Type} (count length : Usize)
    (effects : Effects α β γ) (observed : IndexState)
    (ran : sourceState_3_24928 count length effects = .ok (some observed))
    (normal first second : Result δ) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_index_certificate .indexPrecondition count length effects observed ran normal first second
#print axioms certificate_3_24928
/-- Actual LLBC instance 370:e926d80d1d048ac77607, source instruction 30822. -/
def sourceState_3_30822 {α β γ : Type} (count length : Usize)
    (effects : Effects α β γ) : Result (Option IndexState) := sourceEvent .index count length effects
theorem certificate_3_30822 {α β γ δ : Type} (count length : Usize)
    (effects : Effects α β γ) (observed : IndexState)
    (ran : sourceState_3_30822 count length effects = .ok (some observed))
    (normal first second : Result δ) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_index_certificate .index count length effects observed ran normal first second
#print axioms certificate_3_30822
/-- Actual LLBC instance 370:e926d80d1d048ac77607, source instruction 24973. -/
def sourceState_3_24973 {α β γ : Type} (count length : Usize)
    (effects : Effects α β γ) : Result (Option IndexState) := sourceEvent .addPrecondition count length effects
theorem certificate_3_24973 {α β γ δ : Type} (count length : Usize)
    (effects : Effects α β γ) (observed : IndexState)
    (ran : sourceState_3_24973 count length effects = .ok (some observed))
    (normal first second : Result δ) :
    ¬ diagnostic (arithmeticGuard (.add observed.index 1 (UScalar.max .Usize))) ∧
      branch (arithmeticGuard (.add observed.index 1 (UScalar.max .Usize))) normal first = branch (arithmeticGuard (.add observed.index 1 (UScalar.max .Usize))) normal second :=
  event_add_certificate count length effects observed ran normal first second
#print axioms certificate_3_24973
/-- Actual LLBC instance 370:f6ad4bbd3ed0b7c67356, source instruction 24928. -/
def sourceState_4_24928 {α β γ : Type} (count length : Usize)
    (effects : Effects α β γ) : Result (Option IndexState) := sourceEvent .indexPrecondition count length effects
theorem certificate_4_24928 {α β γ δ : Type} (count length : Usize)
    (effects : Effects α β γ) (observed : IndexState)
    (ran : sourceState_4_24928 count length effects = .ok (some observed))
    (normal first second : Result δ) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_index_certificate .indexPrecondition count length effects observed ran normal first second
#print axioms certificate_4_24928
/-- Actual LLBC instance 370:f6ad4bbd3ed0b7c67356, source instruction 30822. -/
def sourceState_4_30822 {α β γ : Type} (count length : Usize)
    (effects : Effects α β γ) : Result (Option IndexState) := sourceEvent .index count length effects
theorem certificate_4_30822 {α β γ δ : Type} (count length : Usize)
    (effects : Effects α β γ) (observed : IndexState)
    (ran : sourceState_4_30822 count length effects = .ok (some observed))
    (normal first second : Result δ) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_index_certificate .index count length effects observed ran normal first second
#print axioms certificate_4_30822
/-- Actual LLBC instance 370:f6ad4bbd3ed0b7c67356, source instruction 24973. -/
def sourceState_4_24973 {α β γ : Type} (count length : Usize)
    (effects : Effects α β γ) : Result (Option IndexState) := sourceEvent .addPrecondition count length effects
theorem certificate_4_24973 {α β γ δ : Type} (count length : Usize)
    (effects : Effects α β γ) (observed : IndexState)
    (ran : sourceState_4_24973 count length effects = .ok (some observed))
    (normal first second : Result δ) :
    ¬ diagnostic (arithmeticGuard (.add observed.index 1 (UScalar.max .Usize))) ∧
      branch (arithmeticGuard (.add observed.index 1 (UScalar.max .Usize))) normal first = branch (arithmeticGuard (.add observed.index 1 (UScalar.max .Usize))) normal second :=
  event_add_certificate count length effects observed ran normal first second
#print axioms certificate_4_24973
/-- Actual LLBC instance 370:a47de7e54a694dd49fe7, source instruction 24928. -/
def sourceState_5_24928 {α β γ : Type} (count length : Usize)
    (effects : Effects α β γ) : Result (Option IndexState) := sourceEvent .indexPrecondition count length effects
theorem certificate_5_24928 {α β γ δ : Type} (count length : Usize)
    (effects : Effects α β γ) (observed : IndexState)
    (ran : sourceState_5_24928 count length effects = .ok (some observed))
    (normal first second : Result δ) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_index_certificate .indexPrecondition count length effects observed ran normal first second
#print axioms certificate_5_24928
/-- Actual LLBC instance 370:a47de7e54a694dd49fe7, source instruction 30822. -/
def sourceState_5_30822 {α β γ : Type} (count length : Usize)
    (effects : Effects α β γ) : Result (Option IndexState) := sourceEvent .index count length effects
theorem certificate_5_30822 {α β γ δ : Type} (count length : Usize)
    (effects : Effects α β γ) (observed : IndexState)
    (ran : sourceState_5_30822 count length effects = .ok (some observed))
    (normal first second : Result δ) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_index_certificate .index count length effects observed ran normal first second
#print axioms certificate_5_30822
/-- Actual LLBC instance 370:a47de7e54a694dd49fe7, source instruction 24973. -/
def sourceState_5_24973 {α β γ : Type} (count length : Usize)
    (effects : Effects α β γ) : Result (Option IndexState) := sourceEvent .addPrecondition count length effects
theorem certificate_5_24973 {α β γ δ : Type} (count length : Usize)
    (effects : Effects α β γ) (observed : IndexState)
    (ran : sourceState_5_24973 count length effects = .ok (some observed))
    (normal first second : Result δ) :
    ¬ diagnostic (arithmeticGuard (.add observed.index 1 (UScalar.max .Usize))) ∧
      branch (arithmeticGuard (.add observed.index 1 (UScalar.max .Usize))) normal first = branch (arithmeticGuard (.add observed.index 1 (UScalar.max .Usize))) normal second :=
  event_add_certificate count length effects observed ran normal first second
#print axioms certificate_5_24973
/-- Actual LLBC instance 370:c9511bced1e57010b514, source instruction 24928. -/
def sourceState_6_24928 {α β γ : Type} (count length : Usize)
    (effects : Effects α β γ) : Result (Option IndexState) := sourceEvent .indexPrecondition count length effects
theorem certificate_6_24928 {α β γ δ : Type} (count length : Usize)
    (effects : Effects α β γ) (observed : IndexState)
    (ran : sourceState_6_24928 count length effects = .ok (some observed))
    (normal first second : Result δ) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_index_certificate .indexPrecondition count length effects observed ran normal first second
#print axioms certificate_6_24928
/-- Actual LLBC instance 370:c9511bced1e57010b514, source instruction 30822. -/
def sourceState_6_30822 {α β γ : Type} (count length : Usize)
    (effects : Effects α β γ) : Result (Option IndexState) := sourceEvent .index count length effects
theorem certificate_6_30822 {α β γ δ : Type} (count length : Usize)
    (effects : Effects α β γ) (observed : IndexState)
    (ran : sourceState_6_30822 count length effects = .ok (some observed))
    (normal first second : Result δ) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_index_certificate .index count length effects observed ran normal first second
#print axioms certificate_6_30822
/-- Actual LLBC instance 370:c9511bced1e57010b514, source instruction 24973. -/
def sourceState_6_24973 {α β γ : Type} (count length : Usize)
    (effects : Effects α β γ) : Result (Option IndexState) := sourceEvent .addPrecondition count length effects
theorem certificate_6_24973 {α β γ δ : Type} (count length : Usize)
    (effects : Effects α β γ) (observed : IndexState)
    (ran : sourceState_6_24973 count length effects = .ok (some observed))
    (normal first second : Result δ) :
    ¬ diagnostic (arithmeticGuard (.add observed.index 1 (UScalar.max .Usize))) ∧
      branch (arithmeticGuard (.add observed.index 1 (UScalar.max .Usize))) normal first = branch (arithmeticGuard (.add observed.index 1 (UScalar.max .Usize))) normal second :=
  event_add_certificate count length effects observed ran normal first second
#print axioms certificate_6_24973
/-- Actual LLBC instance 370:55b585cb1a3453ec2417, source instruction 24928. -/
def sourceState_7_24928 {α β γ : Type} (count length : Usize)
    (effects : Effects α β γ) : Result (Option IndexState) := sourceEvent .indexPrecondition count length effects
theorem certificate_7_24928 {α β γ δ : Type} (count length : Usize)
    (effects : Effects α β γ) (observed : IndexState)
    (ran : sourceState_7_24928 count length effects = .ok (some observed))
    (normal first second : Result δ) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_index_certificate .indexPrecondition count length effects observed ran normal first second
#print axioms certificate_7_24928
/-- Actual LLBC instance 370:55b585cb1a3453ec2417, source instruction 30822. -/
def sourceState_7_30822 {α β γ : Type} (count length : Usize)
    (effects : Effects α β γ) : Result (Option IndexState) := sourceEvent .index count length effects
theorem certificate_7_30822 {α β γ δ : Type} (count length : Usize)
    (effects : Effects α β γ) (observed : IndexState)
    (ran : sourceState_7_30822 count length effects = .ok (some observed))
    (normal first second : Result δ) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_index_certificate .index count length effects observed ran normal first second
#print axioms certificate_7_30822
/-- Actual LLBC instance 370:55b585cb1a3453ec2417, source instruction 24973. -/
def sourceState_7_24973 {α β γ : Type} (count length : Usize)
    (effects : Effects α β γ) : Result (Option IndexState) := sourceEvent .addPrecondition count length effects
theorem certificate_7_24973 {α β γ δ : Type} (count length : Usize)
    (effects : Effects α β γ) (observed : IndexState)
    (ran : sourceState_7_24973 count length effects = .ok (some observed))
    (normal first second : Result δ) :
    ¬ diagnostic (arithmeticGuard (.add observed.index 1 (UScalar.max .Usize))) ∧
      branch (arithmeticGuard (.add observed.index 1 (UScalar.max .Usize))) normal first = branch (arithmeticGuard (.add observed.index 1 (UScalar.max .Usize))) normal second :=
  event_add_certificate count length effects observed ran normal first second
#print axioms certificate_7_24973
/-- Actual LLBC instance 370:bf6cea38780548e61105, source instruction 24928. -/
def sourceState_8_24928 {α β γ : Type} (count length : Usize)
    (effects : Effects α β γ) : Result (Option IndexState) := sourceEvent .indexPrecondition count length effects
theorem certificate_8_24928 {α β γ δ : Type} (count length : Usize)
    (effects : Effects α β γ) (observed : IndexState)
    (ran : sourceState_8_24928 count length effects = .ok (some observed))
    (normal first second : Result δ) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_index_certificate .indexPrecondition count length effects observed ran normal first second
#print axioms certificate_8_24928
/-- Actual LLBC instance 370:bf6cea38780548e61105, source instruction 30822. -/
def sourceState_8_30822 {α β γ : Type} (count length : Usize)
    (effects : Effects α β γ) : Result (Option IndexState) := sourceEvent .index count length effects
theorem certificate_8_30822 {α β γ δ : Type} (count length : Usize)
    (effects : Effects α β γ) (observed : IndexState)
    (ran : sourceState_8_30822 count length effects = .ok (some observed))
    (normal first second : Result δ) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_index_certificate .index count length effects observed ran normal first second
#print axioms certificate_8_30822
/-- Actual LLBC instance 370:bf6cea38780548e61105, source instruction 24973. -/
def sourceState_8_24973 {α β γ : Type} (count length : Usize)
    (effects : Effects α β γ) : Result (Option IndexState) := sourceEvent .addPrecondition count length effects
theorem certificate_8_24973 {α β γ δ : Type} (count length : Usize)
    (effects : Effects α β γ) (observed : IndexState)
    (ran : sourceState_8_24973 count length effects = .ok (some observed))
    (normal first second : Result δ) :
    ¬ diagnostic (arithmeticGuard (.add observed.index 1 (UScalar.max .Usize))) ∧
      branch (arithmeticGuard (.add observed.index 1 (UScalar.max .Usize))) normal first = branch (arithmeticGuard (.add observed.index 1 (UScalar.max .Usize))) normal second :=
  event_add_certificate count length effects observed ran normal first second
#print axioms certificate_8_24973
/-- Actual LLBC instance 370:5f084939c1b0b4851e22, source instruction 24928. -/
def sourceState_9_24928 {α β γ : Type} (count length : Usize)
    (effects : Effects α β γ) : Result (Option IndexState) := sourceEvent .indexPrecondition count length effects
theorem certificate_9_24928 {α β γ δ : Type} (count length : Usize)
    (effects : Effects α β γ) (observed : IndexState)
    (ran : sourceState_9_24928 count length effects = .ok (some observed))
    (normal first second : Result δ) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_index_certificate .indexPrecondition count length effects observed ran normal first second
#print axioms certificate_9_24928
/-- Actual LLBC instance 370:5f084939c1b0b4851e22, source instruction 30822. -/
def sourceState_9_30822 {α β γ : Type} (count length : Usize)
    (effects : Effects α β γ) : Result (Option IndexState) := sourceEvent .index count length effects
theorem certificate_9_30822 {α β γ δ : Type} (count length : Usize)
    (effects : Effects α β γ) (observed : IndexState)
    (ran : sourceState_9_30822 count length effects = .ok (some observed))
    (normal first second : Result δ) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_index_certificate .index count length effects observed ran normal first second
#print axioms certificate_9_30822
/-- Actual LLBC instance 370:5f084939c1b0b4851e22, source instruction 24973. -/
def sourceState_9_24973 {α β γ : Type} (count length : Usize)
    (effects : Effects α β γ) : Result (Option IndexState) := sourceEvent .addPrecondition count length effects
theorem certificate_9_24973 {α β γ δ : Type} (count length : Usize)
    (effects : Effects α β γ) (observed : IndexState)
    (ran : sourceState_9_24973 count length effects = .ok (some observed))
    (normal first second : Result δ) :
    ¬ diagnostic (arithmeticGuard (.add observed.index 1 (UScalar.max .Usize))) ∧
      branch (arithmeticGuard (.add observed.index 1 (UScalar.max .Usize))) normal first = branch (arithmeticGuard (.add observed.index 1 (UScalar.max .Usize))) normal second :=
  event_add_certificate count length effects observed ran normal first second
#print axioms certificate_9_24973
/-- Actual LLBC instance 370:9af7480c5abd94feb76b, source instruction 24928. -/
def sourceState_10_24928 {α β γ : Type} (count length : Usize)
    (effects : Effects α β γ) : Result (Option IndexState) := sourceEvent .indexPrecondition count length effects
theorem certificate_10_24928 {α β γ δ : Type} (count length : Usize)
    (effects : Effects α β γ) (observed : IndexState)
    (ran : sourceState_10_24928 count length effects = .ok (some observed))
    (normal first second : Result δ) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_index_certificate .indexPrecondition count length effects observed ran normal first second
#print axioms certificate_10_24928
/-- Actual LLBC instance 370:9af7480c5abd94feb76b, source instruction 30822. -/
def sourceState_10_30822 {α β γ : Type} (count length : Usize)
    (effects : Effects α β γ) : Result (Option IndexState) := sourceEvent .index count length effects
theorem certificate_10_30822 {α β γ δ : Type} (count length : Usize)
    (effects : Effects α β γ) (observed : IndexState)
    (ran : sourceState_10_30822 count length effects = .ok (some observed))
    (normal first second : Result δ) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_index_certificate .index count length effects observed ran normal first second
#print axioms certificate_10_30822
/-- Actual LLBC instance 370:9af7480c5abd94feb76b, source instruction 24973. -/
def sourceState_10_24973 {α β γ : Type} (count length : Usize)
    (effects : Effects α β γ) : Result (Option IndexState) := sourceEvent .addPrecondition count length effects
theorem certificate_10_24973 {α β γ δ : Type} (count length : Usize)
    (effects : Effects α β γ) (observed : IndexState)
    (ran : sourceState_10_24973 count length effects = .ok (some observed))
    (normal first second : Result δ) :
    ¬ diagnostic (arithmeticGuard (.add observed.index 1 (UScalar.max .Usize))) ∧
      branch (arithmeticGuard (.add observed.index 1 (UScalar.max .Usize))) normal first = branch (arithmeticGuard (.add observed.index 1 (UScalar.max .Usize))) normal second :=
  event_add_certificate count length effects observed ran normal first second
#print axioms certificate_10_24973
/-- Actual LLBC instance 370:5c2390cd4fa87e7aab86, source instruction 24928. -/
def sourceState_11_24928 {α β γ : Type} (count length : Usize)
    (effects : Effects α β γ) : Result (Option IndexState) := sourceEvent .indexPrecondition count length effects
theorem certificate_11_24928 {α β γ δ : Type} (count length : Usize)
    (effects : Effects α β γ) (observed : IndexState)
    (ran : sourceState_11_24928 count length effects = .ok (some observed))
    (normal first second : Result δ) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_index_certificate .indexPrecondition count length effects observed ran normal first second
#print axioms certificate_11_24928
/-- Actual LLBC instance 370:5c2390cd4fa87e7aab86, source instruction 30822. -/
def sourceState_11_30822 {α β γ : Type} (count length : Usize)
    (effects : Effects α β γ) : Result (Option IndexState) := sourceEvent .index count length effects
theorem certificate_11_30822 {α β γ δ : Type} (count length : Usize)
    (effects : Effects α β γ) (observed : IndexState)
    (ran : sourceState_11_30822 count length effects = .ok (some observed))
    (normal first second : Result δ) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_index_certificate .index count length effects observed ran normal first second
#print axioms certificate_11_30822
/-- Actual LLBC instance 370:5c2390cd4fa87e7aab86, source instruction 24973. -/
def sourceState_11_24973 {α β γ : Type} (count length : Usize)
    (effects : Effects α β γ) : Result (Option IndexState) := sourceEvent .addPrecondition count length effects
theorem certificate_11_24973 {α β γ δ : Type} (count length : Usize)
    (effects : Effects α β γ) (observed : IndexState)
    (ran : sourceState_11_24973 count length effects = .ok (some observed))
    (normal first second : Result δ) :
    ¬ diagnostic (arithmeticGuard (.add observed.index 1 (UScalar.max .Usize))) ∧
      branch (arithmeticGuard (.add observed.index 1 (UScalar.max .Usize))) normal first = branch (arithmeticGuard (.add observed.index 1 (UScalar.max .Usize))) normal second :=
  event_add_certificate count length effects observed ran normal first second
#print axioms certificate_11_24973
/-- Actual LLBC instance 370:064f068c4fd99709434e, source instruction 24928. -/
def sourceState_12_24928 {α β γ : Type} (count length : Usize)
    (effects : Effects α β γ) : Result (Option IndexState) := sourceEvent .indexPrecondition count length effects
theorem certificate_12_24928 {α β γ δ : Type} (count length : Usize)
    (effects : Effects α β γ) (observed : IndexState)
    (ran : sourceState_12_24928 count length effects = .ok (some observed))
    (normal first second : Result δ) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_index_certificate .indexPrecondition count length effects observed ran normal first second
#print axioms certificate_12_24928
/-- Actual LLBC instance 370:064f068c4fd99709434e, source instruction 30822. -/
def sourceState_12_30822 {α β γ : Type} (count length : Usize)
    (effects : Effects α β γ) : Result (Option IndexState) := sourceEvent .index count length effects
theorem certificate_12_30822 {α β γ δ : Type} (count length : Usize)
    (effects : Effects α β γ) (observed : IndexState)
    (ran : sourceState_12_30822 count length effects = .ok (some observed))
    (normal first second : Result δ) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_index_certificate .index count length effects observed ran normal first second
#print axioms certificate_12_30822
/-- Actual LLBC instance 370:064f068c4fd99709434e, source instruction 24973. -/
def sourceState_12_24973 {α β γ : Type} (count length : Usize)
    (effects : Effects α β γ) : Result (Option IndexState) := sourceEvent .addPrecondition count length effects
theorem certificate_12_24973 {α β γ δ : Type} (count length : Usize)
    (effects : Effects α β γ) (observed : IndexState)
    (ran : sourceState_12_24973 count length effects = .ok (some observed))
    (normal first second : Result δ) :
    ¬ diagnostic (arithmeticGuard (.add observed.index 1 (UScalar.max .Usize))) ∧
      branch (arithmeticGuard (.add observed.index 1 (UScalar.max .Usize))) normal first = branch (arithmeticGuard (.add observed.index 1 (UScalar.max .Usize))) normal second :=
  event_add_certificate count length effects observed ran normal first second
#print axioms certificate_12_24973
/-- Actual LLBC instance 370:b9ac39bc24063a5fa2e1, source instruction 24928. -/
def sourceState_13_24928 {α β γ : Type} (count length : Usize)
    (effects : Effects α β γ) : Result (Option IndexState) := sourceEvent .indexPrecondition count length effects
theorem certificate_13_24928 {α β γ δ : Type} (count length : Usize)
    (effects : Effects α β γ) (observed : IndexState)
    (ran : sourceState_13_24928 count length effects = .ok (some observed))
    (normal first second : Result δ) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_index_certificate .indexPrecondition count length effects observed ran normal first second
#print axioms certificate_13_24928
/-- Actual LLBC instance 370:b9ac39bc24063a5fa2e1, source instruction 30822. -/
def sourceState_13_30822 {α β γ : Type} (count length : Usize)
    (effects : Effects α β γ) : Result (Option IndexState) := sourceEvent .index count length effects
theorem certificate_13_30822 {α β γ δ : Type} (count length : Usize)
    (effects : Effects α β γ) (observed : IndexState)
    (ran : sourceState_13_30822 count length effects = .ok (some observed))
    (normal first second : Result δ) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_index_certificate .index count length effects observed ran normal first second
#print axioms certificate_13_30822
/-- Actual LLBC instance 370:b9ac39bc24063a5fa2e1, source instruction 24973. -/
def sourceState_13_24973 {α β γ : Type} (count length : Usize)
    (effects : Effects α β γ) : Result (Option IndexState) := sourceEvent .addPrecondition count length effects
theorem certificate_13_24973 {α β γ δ : Type} (count length : Usize)
    (effects : Effects α β γ) (observed : IndexState)
    (ran : sourceState_13_24973 count length effects = .ok (some observed))
    (normal first second : Result δ) :
    ¬ diagnostic (arithmeticGuard (.add observed.index 1 (UScalar.max .Usize))) ∧
      branch (arithmeticGuard (.add observed.index 1 (UScalar.max .Usize))) normal first = branch (arithmeticGuard (.add observed.index 1 (UScalar.max .Usize))) normal second :=
  event_add_certificate count length effects observed ran normal first second
#print axioms certificate_13_24973
/-- Actual LLBC instance 370:b2a3dc1fdf10716d1e9c, source instruction 24928. -/
def sourceState_14_24928 {α β γ : Type} (count length : Usize)
    (effects : Effects α β γ) : Result (Option IndexState) := sourceEvent .indexPrecondition count length effects
theorem certificate_14_24928 {α β γ δ : Type} (count length : Usize)
    (effects : Effects α β γ) (observed : IndexState)
    (ran : sourceState_14_24928 count length effects = .ok (some observed))
    (normal first second : Result δ) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_index_certificate .indexPrecondition count length effects observed ran normal first second
#print axioms certificate_14_24928
/-- Actual LLBC instance 370:b2a3dc1fdf10716d1e9c, source instruction 30822. -/
def sourceState_14_30822 {α β γ : Type} (count length : Usize)
    (effects : Effects α β γ) : Result (Option IndexState) := sourceEvent .index count length effects
theorem certificate_14_30822 {α β γ δ : Type} (count length : Usize)
    (effects : Effects α β γ) (observed : IndexState)
    (ran : sourceState_14_30822 count length effects = .ok (some observed))
    (normal first second : Result δ) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_index_certificate .index count length effects observed ran normal first second
#print axioms certificate_14_30822
/-- Actual LLBC instance 370:b2a3dc1fdf10716d1e9c, source instruction 24973. -/
def sourceState_14_24973 {α β γ : Type} (count length : Usize)
    (effects : Effects α β γ) : Result (Option IndexState) := sourceEvent .addPrecondition count length effects
theorem certificate_14_24973 {α β γ δ : Type} (count length : Usize)
    (effects : Effects α β γ) (observed : IndexState)
    (ran : sourceState_14_24973 count length effects = .ok (some observed))
    (normal first second : Result δ) :
    ¬ diagnostic (arithmeticGuard (.add observed.index 1 (UScalar.max .Usize))) ∧
      branch (arithmeticGuard (.add observed.index 1 (UScalar.max .Usize))) normal first = branch (arithmeticGuard (.add observed.index 1 (UScalar.max .Usize))) normal second :=
  event_add_certificate count length effects observed ran normal first second
#print axioms certificate_14_24973
/-- Actual LLBC instance 370:8874698bbea8bd4a8b04, source instruction 24928. -/
def sourceState_15_24928 {α β γ : Type} (count length : Usize)
    (effects : Effects α β γ) : Result (Option IndexState) := sourceEvent .indexPrecondition count length effects
theorem certificate_15_24928 {α β γ δ : Type} (count length : Usize)
    (effects : Effects α β γ) (observed : IndexState)
    (ran : sourceState_15_24928 count length effects = .ok (some observed))
    (normal first second : Result δ) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_index_certificate .indexPrecondition count length effects observed ran normal first second
#print axioms certificate_15_24928
/-- Actual LLBC instance 370:8874698bbea8bd4a8b04, source instruction 30822. -/
def sourceState_15_30822 {α β γ : Type} (count length : Usize)
    (effects : Effects α β γ) : Result (Option IndexState) := sourceEvent .index count length effects
theorem certificate_15_30822 {α β γ δ : Type} (count length : Usize)
    (effects : Effects α β γ) (observed : IndexState)
    (ran : sourceState_15_30822 count length effects = .ok (some observed))
    (normal first second : Result δ) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  event_index_certificate .index count length effects observed ran normal first second
#print axioms certificate_15_30822
/-- Actual LLBC instance 370:8874698bbea8bd4a8b04, source instruction 24973. -/
def sourceState_15_24973 {α β γ : Type} (count length : Usize)
    (effects : Effects α β γ) : Result (Option IndexState) := sourceEvent .addPrecondition count length effects
theorem certificate_15_24973 {α β γ δ : Type} (count length : Usize)
    (effects : Effects α β γ) (observed : IndexState)
    (ran : sourceState_15_24973 count length effects = .ok (some observed))
    (normal first second : Result δ) :
    ¬ diagnostic (arithmeticGuard (.add observed.index 1 (UScalar.max .Usize))) ∧
      branch (arithmeticGuard (.add observed.index 1 (UScalar.max .Usize))) normal first = branch (arithmeticGuard (.add observed.index 1 (UScalar.max .Usize))) normal second :=
  event_add_certificate count length effects observed ran normal first second
#print axioms certificate_15_24973
end PV_B3P_InitializerFamily578227
