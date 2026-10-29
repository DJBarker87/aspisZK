import PV_DIAG6_Prefix
import R0Z.FsAbortBounds
/-! Original-L1-coordinate handoff, using the existing finite law/mass
operators. No new coins, bad event, epsilon or trust field. Native event,
terminal and prefix-family laws remain explicit P hypotheses. -/
set_option autoImplicit false
noncomputable section
namespace PV_DIAG6
open PV_DIAG3 R0Z R0Z.FsAbortBounds
variable {S A W R P C O : Type}
def diagnosticPieces (count : Nat) (x : Execution S A) := (count,x.events,x.exit)
-- STAGE
theorem pieces_of_joint_execution (rel : S → S → Prop) (a b : Execution S A)
 (m n : Nat) (hc : m = n) (h : Coupled rel a b) :
 diagnosticPieces m a = diagnosticPieces n b := by
 unfold diagnosticPieces
 rw [hc,h.1,h.2.2]
#print axioms pieces_of_joint_execution
-- STAGE
theorem pieces_iff (a b : Execution S A) (m n : Nat) :
 diagnosticPieces m a = diagnosticPieces n b ↔ m = n ∧ a.events = b.events ∧ a.exit = b.exit := by
 constructor
 · intro h
   exact ⟨congrArg (fun p => p.1) h,congrArg (fun p => p.2.1) h,congrArg (fun p => p.2.2) h⟩
 · rintro ⟨hc,he,ht⟩
   unfold diagnosticPieces; rw [hc,he,ht]
#print axioms pieces_iff
-- STAGE
theorem honest_joint_native (honest : W → Prop) (pub : W → P) (coins : W → R → C)
 (actualCount : W → R → Nat) (l1Count : P → C → Nat)
 (actual : W → R → Execution S A) (events : P → C → List Event) (terminal : P → C → Exit A)
 (existingL1Count : ∀ w r, honest w → actualCount w r = l1Count (pub w) (coins w r))
 (nativeDiagnosticLaw : ∀ w r, honest w → (actual w r).events = events (pub w) (coins w r))
 (nativeTerminalLaw : ∀ w r, honest w → (actual w r).exit = terminal (pub w) (coins w r))
 (w : W) (r : R) (hw : honest w) :
 diagnosticPieces (actualCount w r) (actual w r) =
 (l1Count (pub w) (coins w r),events (pub w) (coins w r),terminal (pub w) (coins w r)) := by
 unfold diagnosticPieces
 rw [existingL1Count w r hw,nativeDiagnosticLaw w r hw,nativeTerminalLaw w r hw]
#print axioms honest_joint_native
-- STAGE
theorem honest_joint_function (left right : R → Nat × List Event × Exit A)
 (pointwise : ∀ r, left r = right r) : left = right := funext pointwise
#print axioms honest_joint_function
-- STAGE
theorem whole_diagnostic_law [Fintype R]
 (left right : R → Nat × List Event × Exit A) (joint : ∀ r, left r = right r) :
 EqualLaws left right := by
 have h : left = right := funext joint
 rw [h]
 intro value; rfl
#print axioms whole_diagnostic_law
-- STAGE
theorem whole_diagnostic_tests [Fintype R]
 (left right : R → Nat × List Event × Exit A) (joint : ∀ r, left r = right r)
 (test : Nat × List Event × Exit A → Prop) :
 mass (fun r => test (left r)) = mass (fun r => test (right r)) := by
 apply mass_congr
 intro r; rw [joint r]
#print axioms whole_diagnostic_tests
-- STAGE
theorem whole_diagnostic_expectations [Fintype R]
 (left right : R → Nat × List Event × Exit A) (joint : ∀ r, left r = right r)
 (test : Nat × List Event × Exit A → ℚ) :
 mean (fun r => test (left r)) = mean (fun r => test (right r)) := by
 exact LawTransport.mean_eq_of_equalLaws left right test (whole_diagnostic_law left right joint)
#print axioms whole_diagnostic_expectations
-- STAGE
theorem existing_count_marginal [Fintype R] (actual ideal : R → Nat)
 (existingL1Count : ∀ r, actual r = ideal r) : EqualLaws actual ideal := by
 have h : actual = ideal := funext existingL1Count
 rw [h]; intro value; rfl
#print axioms existing_count_marginal
-- STAGE
theorem count_terminal_joint [Fintype R] (actual ideal : R → Nat)
 (a b : R → Exit A) (existingL1Count : ∀ r, actual r = ideal r)
 (nativeTerminalLaw : ∀ r, a r = b r) :
 EqualLaws (fun r => (actual r,a r)) (fun r => (ideal r,b r)) := by
 have h : (fun r => (actual r,a r)) = (fun r => (ideal r,b r)) := by
   funext r; rw [existingL1Count r,nativeTerminalLaw r]
 rw [h]; intro value; rfl
#print axioms count_terminal_joint
-- STAGE
theorem same_original_coordinates (count : P → C → Nat)
 (events : P → C → List Event) (terminal : P → C → Exit A)
 (p q : P) (c d : C) (hp : p = q) (hc : c = d) :
 (count p c,events p c,terminal p c) = (count q d,events q d,terminal q d) := by
 cases hp; cases hc; rfl
#print axioms same_original_coordinates
-- STAGE
theorem all_prefixes_joint_function (count actualCount : R → Nat)
 (a b : R → PrefixFamily S A) (hc : ∀ r, actualCount r = count r)
 (he : ∀ r n, ((a r).sample n).events = ((b r).sample n).events)
 (ht : ∀ r n, ((a r).sample n).exit = ((b r).sample n).exit) :
 (fun r n => diagnosticPieces (actualCount r) ((a r).sample n)) =
 (fun r n => diagnosticPieces (count r) ((b r).sample n)) := by
 funext r n
 unfold diagnosticPieces; rw [hc r,he r n,ht r n]
#print axioms all_prefixes_joint_function
-- STAGE
theorem whole_prefix_family_law [Fintype R]
 (a b : R → Nat → Nat × List Event × Exit A) (h : ∀ r n, a r n = b r n) :
 EqualLaws a b := by
 have hab : a = b := by funext r n; exact h r n
 rw [hab]; intro value; rfl
#print axioms whole_prefix_family_law
-- STAGE
theorem whole_prefix_family_tests [Fintype R]
 (a b : R → Nat → Nat × List Event × Exit A) (h : ∀ r n, a r n = b r n)
 (test : (Nat → Nat × List Event × Exit A) → Prop) :
 mass (fun r => test (a r)) = mass (fun r => test (b r)) := by
 apply mass_congr
 intro r
 have hr : a r = b r := funext (h r)
 rw [hr]
#print axioms whole_prefix_family_tests
-- STAGE
theorem family_law_to_fixed_prefix [Fintype R]
 (a b : R → Nat → Nat × List Event × Exit A) (h : ∀ r n, a r n = b r n) (n : Nat) :
 EqualLaws (fun r => a r n) (fun r => b r n) :=
 whole_diagnostic_law _ _ (fun r => h r n)
#print axioms family_law_to_fixed_prefix
-- STAGE
theorem family_decoder_recovery (recover : Execution S A → List Event)
 (lossless : ∀ x, recover x = x.events) (a : R → PrefixFamily S A) :
 (fun r n => recover ((a r).sample n)) = (fun r n => ((a r).sample n).events) := by
 funext r n; exact lossless _
#print axioms family_decoder_recovery
-- STAGE
theorem decoder_whole_prefix_law [Fintype R]
 (recover : Execution S A → List Event) (lossless : ∀ x, recover x = x.events)
 (a b : R → PrefixFamily S A)
 (h : ∀ r n, ((a r).sample n).events = ((b r).sample n).events) :
 EqualLaws (fun r n => recover ((a r).sample n))
 (fun r n => recover ((b r).sample n)) := by
 have hab : (fun r n => recover ((a r).sample n)) =
     (fun r n => recover ((b r).sample n)) := by
   funext r n; rw [lossless,lossless,h r n]
 rw [hab]; intro value; rfl
#print axioms decoder_whole_prefix_law
-- STAGE
theorem failure_signal_transport [Fintype R]
 (a b : R → Exit A) (terminalLaw : ∀ r, a r = b r) (failure : Exit A → Prop) :
 mass (fun r => failure (a r)) = mass (fun r => failure (b r)) := by
 apply mass_congr
 intro r; rw [terminalLaw r]
#print axioms failure_signal_transport
-- STAGE
theorem failure_and_emitted_prefix_transport [Fintype R]
 (a b : R → Execution S A) (he : ∀ r, (a r).events = (b r).events)
 (ht : ∀ r, (a r).exit = (b r).exit)
 (test : List Event → Exit A → Prop) :
 mass (fun r => test (a r).events (a r).exit) =
 mass (fun r => test (b r).events (b r).exit) := by
 apply mass_congr
 intro r; rw [he r,ht r]
#print axioms failure_and_emitted_prefix_transport
-- STAGE
theorem count_and_frames_joint [Fintype R]
 (a b : R → Execution S A) (m n : R → Nat)
 (hc : ∀ r, m r = n r) (he : ∀ r, (a r).events = (b r).events) :
 EqualLaws (fun r => (m r,selectedFrames (a r).events))
 (fun r => (n r,selectedFrames (b r).events)) := by
 have h : (fun r => (m r,selectedFrames (a r).events)) =
     (fun r => (n r,selectedFrames (b r).events)) := by
   funext r; rw [hc r,he r]
 rw [h]; intro value; rfl
#print axioms count_and_frames_joint
-- STAGE
theorem requested_delivered_joint [Fintype R]
 (a b : R → Execution S A) (he : ∀ r, (a r).events = (b r).events) :
 EqualLaws (fun r => (requestedBytes (a r).events,deliveredBytes (a r).events))
 (fun r => (requestedBytes (b r).events,deliveredBytes (b r).events)) := by
 have h : (fun r => (requestedBytes (a r).events,deliveredBytes (a r).events)) =
     (fun r => (requestedBytes (b r).events,deliveredBytes (b r).events)) := by
   funext r; rw [he r]
 rw [h]; intro value; rfl
#print axioms requested_delivered_joint
-- STAGE
theorem decoder_and_decision_joint
 (decode : List Event → Exit A → O) (decision : O → Bool)
 (a b : Execution S A) (he : a.events = b.events) (ht : a.exit = b.exit) :
 (decode a.events a.exit,decision (decode a.events a.exit)) =
 (decode b.events b.exit,decision (decode b.events b.exit)) := by rw [he,ht]
#print axioms decoder_and_decision_joint
-- STAGE
theorem decoder_decision_whole_law
 [Fintype R] (decode : List Event → Exit A → O) (decision : O → Bool)
 (a b : R → Execution S A) (he : ∀ r, (a r).events = (b r).events)
 (ht : ∀ r, (a r).exit = (b r).exit) :
 EqualLaws (fun r => (decode (a r).events (a r).exit,decision (decode (a r).events (a r).exit)))
 (fun r => (decode (b r).events (b r).exit,decision (decode (b r).events (b r).exit))) := by
 have h := fun r => decoder_and_decision_joint decode decision (a r) (b r) (he r) (ht r)
 have hh : (fun r => (decode (a r).events (a r).exit,decision (decode (a r).events (a r).exit))) =
     (fun r => (decode (b r).events (b r).exit,decision (decode (b r).events (b r).exit))) := funext h
 rw [hh]; intro value; rfl
#print axioms decoder_decision_whole_law
-- STAGE
theorem decoder_family_decision_law
 [Fintype R] (decode : List Event → Exit A → O)
 (decision : (Nat → O) → Bool) (a b : R → PrefixFamily S A)
 (he : ∀ r n, ((a r).sample n).events = ((b r).sample n).events)
 (ht : ∀ r n, ((a r).sample n).exit = ((b r).sample n).exit) :
 EqualLaws (fun r => decision (fun n => decode ((a r).sample n).events ((a r).sample n).exit))
 (fun r => decision (fun n => decode ((b r).sample n).events ((b r).sample n).exit)) := by
 have hh : (fun r => decision (fun n => decode ((a r).sample n).events ((a r).sample n).exit)) =
     (fun r => decision (fun n => decode ((b r).sample n).events ((b r).sample n).exit)) := by
   funext r
   congr 1
   funext n
   rw [he r n,ht r n]
 rw [hh]; intro value; rfl
#print axioms decoder_family_decision_law
-- STAGE
theorem terminal_law_cannot_be_omitted
 (a b : Execution S A) (m n : Nat)
 (pieces : diagnosticPieces m a = diagnosticPieces n b) : a.exit = b.exit :=
 ((pieces_iff a b m n).mp pieces).2.2
#print axioms terminal_law_cannot_be_omitted
-- STAGE
theorem prefix_law_cannot_be_omitted
 (a b : Execution S A) (m n : Nat)
 (pieces : diagnosticPieces m a = diagnosticPieces n b) : a.events = b.events :=
 ((pieces_iff a b m n).mp pieces).2.1
#print axioms prefix_law_cannot_be_omitted
-- STAGE
theorem failure_with_count_and_prefix
 [Fintype R] (a b : R → Execution S A) (m n : R → Nat)
 (joint : ∀ r, diagnosticPieces (m r) (a r) = diagnosticPieces (n r) (b r))
 (failure : Exit A → Prop) (prior : Nat → List Event → Prop) :
 mass (fun r => prior (m r) (a r).events ∧ failure (a r).exit) =
 mass (fun r => prior (n r) (b r).events ∧ failure (b r).exit) := by
 apply mass_congr
 intro r
 rcases (pieces_iff (a r) (b r) (m r) (n r)).mp (joint r) with ⟨hc,he,ht⟩
 rw [hc,he,ht]
#print axioms failure_with_count_and_prefix
-- STAGE
theorem prefix_family_with_failure_test
 [Fintype R] (a b : R → Nat → Nat × List Event × Exit A)
 (joint : ∀ r n, a r n = b r n) (test : (Nat → Nat × List Event × Exit A) → Prop)
 (failure : R → Prop) :
 mass (fun r => failure r ∧ test (a r)) = mass (fun r => failure r ∧ test (b r)) := by
 apply mass_congr
 intro r
 have h : a r = b r := funext (joint r)
 rw [h]
#print axioms prefix_family_with_failure_test
end PV_DIAG6
