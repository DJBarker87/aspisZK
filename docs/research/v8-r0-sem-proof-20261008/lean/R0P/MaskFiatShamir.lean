import R0P.MaskDuplexDecodes
import R0P.MaskD2Instance
import R0P.MaskD3Glue
import R0P.SemCharP

/-! Generic theorem43 plumbing and the closed 32-round masked instance.
The frozen 31-round specialization is retained without modifying its sources. -/
set_option autoImplicit false
namespace R0P.MaskDuplex
open FS FS2 FS2.Duplex R0C.V3 R0P.SemSource R0P.SemD3Glue R0P.Mask
open AspisV8R19.MemoizedProgramLaw AspisV8PairedCommitment
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
noncomputable section
section Generic
variable {SM : Type} {Sfield : Fin 29 → Subfield SemE} {Pf : Type} {L : Nat}
variable (B : PackBasis (Sfield 0))
variable (p : Duplex.Params (CM SM) (R0C.SemStatement.Chal SemE SemE) L)
variable (x : CX Sfield) (msg : Pf → Nat → CM SM) (decode : CombinedDecode SM Sfield L)
variable (n : Nat)
local notation "prQ" => combinedProtocolAt B p (n + 2) msg decode

/-- Every round starts by absorbing the current message. -/
theorem combinedChainsRead : ChainsRead (prQ) := by
  intro i P m _
  show firstCell (combinedSamplerAt (n + 2 - 1) p i P m) ≠ none
  unfold combinedSamplerAt
  split <;> simp [firstCell, Duplex.samp]

theorem combinedReadsChains (decision : Prefix (CX Sfield) (CM SM) CC → CM SM → Bool) :
    ReadsChains (prQ) (FS2.verifier (prQ) decision) := by
  intro H x π j a hj ha
  exact FS2.verifier_reads (prQ) decision H x π j hj a
    (R0C.V3.DQ.firstCell_mem H _ a ha)

/-- Collisions and generic decoding supply all fields of Inj3. -/
def combinedInj (hrRounds : p.rounds = n + 2)
    (decision : Prefix (CX Sfield) (CM SM) CC → CM SM → Bool)
    (P : Program (Addr L) State Pf) (Qtot : Nat)
    (hQ : ∀ H, FS2.distinctFirstReads (eval H (FS2.experiment P (FS2.verifier (prQ) decision) x)) ≤ Qtot) :
    Inj3 (prQ) (combinedDec p (n + 2) x) P (FS2.verifier (prQ) decision) x κ Qtot where
  Coll := Coll p Qtot
  mass := coll_mass p Qtot P (FS2.verifier (prQ) decision) x hQ
  decodes := fun H hc i a hi ha =>
    combinedDecodes B p x msg decode n hrRounds decision P Qtot hQ H hc i a hi ha

/-- The round count is already generic in theorem43. D1/D2/D3 remain
explicit obligations here; this helper is not the closed masked instance. -/
theorem combined_fiat_shamir_of_obligations (hrRounds : p.rounds = n + 2)
    (decision : Prefix (CX Sfield) (CM SM) CC → CM SM → Bool)
    (rb : RoundByRound' (CX Sfield) (CM SM) CC (Addr L) State)
    (hD1 : FS2.D1 (prQ) rb) (hD2 : FS2.D2 (prQ) rb)
    (hD3 : FS2.D3 (prQ) rb (FS2.verifier (prQ) decision))
    (P : Program (Addr L) State Pf) (Qtot : Nat)
    (hQ : ∀ H, FS2.distinctFirstReads (eval H (FS2.experiment P (FS2.verifier (prQ) decision) x)) ≤ Qtot) :
    mean (fun H : Addr L → State =>
      indicator (FS2.accepts (eval H (FS2.experiment P (FS2.verifier (prQ) decision) x)) ∧
        FS2.extractFails (prQ) x (eval H (FS2.experiment P (FS2.verifier (prQ) decision) x)))) ≤
      (Qtot : ℚ) * maxErr rb.ε (n + 2) + κ Qtot :=
  R0C.V3.theorem43 (prQ) rb (combinedDec p (n + 2) x)
    P (FS2.verifier (prQ) decision) x κ Qtot hD1
    (combinedChainDensity_of_D2 B p (n + 2) x msg decode rb hD2) hD3
    (combinedChainsRead B p msg decode n)
    (combinedReadsChains B p msg decode n decision)
    (combinedInj B p x msg decode n hrRounds decision P Qtot hQ) hQ

#print axioms combinedChainsRead
#print axioms combinedReadsChains
#print axioms combinedInj
#print axioms combined_fiat_shamir_of_obligations
end Generic

/-- Reinstantiate the generic Inj3 proof against the unchanged frozen objects. -/
def combinedInj31 {Sfield : Fin 29 → Subfield SemE} {Pf : Type} {L : Nat}
    (B : PackBasis (Sfield 0))
    (p : Duplex.Params R0P.SemDuplex.CM (ChalZ SemE) L)
    (x : CX Sfield) (msg : Pf → Nat → R0P.SemDuplex.CM)
    (decode : R0P.SemDuplex.CombinedDecode Sfield L) (hr31 : p.rounds = 31)
    (decision : Prefix (CX Sfield) R0P.SemDuplex.CM CC → R0P.SemDuplex.CM → Bool)
    (P : Program (Addr L) State Pf) (Qtot : Nat)
    (hQ : ∀ H, FS2.distinctFirstReads (eval H (FS2.experiment P
      (FS2.verifier (combinedProtocol B p msg decode) decision) x)) ≤ Qtot) :
    Inj3 (combinedProtocol B p msg decode) (R0P.SemDuplex.combinedDec p B x) P
      (FS2.verifier (combinedProtocol B p msg decode) decision) x κ Qtot := by
  simpa only [Nat.reduceAdd, combinedProtocolAt_31, combinedDec_31 p B x] using
    combinedInj B p x msg decode 29 hr31 decision P Qtot hQ

/-- The masked schedule obtains Inj3 at 32 without changing theorem43. -/
def combinedInj32 {Sfield : Fin 29 → Subfield SemE} {Pf : Type} {L : Nat}
    (B : PackBasis (Sfield 0)) (p : Duplex.Params (MsgZ SemE) (ChalZ SemE) L)
    (x : CX Sfield) (msg : Pf → Nat → MsgZ SemE)
    (decode : CombinedDecode (SemMsgZ SemE) Sfield L) (hr32 : p.rounds = 32)
    (decision : Prefix (CX Sfield) (MsgZ SemE) CC → MsgZ SemE → Bool)
    (P : Program (Addr L) State Pf) (Qtot : Nat)
    (hQ : ∀ H, FS2.distinctFirstReads (eval H (FS2.experiment P
      (FS2.verifier (combinedProtocolZ B p msg decode) decision) x)) ≤ Qtot) :
    Inj3 (combinedProtocolZ B p msg decode) (combinedDecZ p x) P
      (FS2.verifier (combinedProtocolZ B p msg decode) decision) x κ Qtot := by
  simpa only [Nat.reduceAdd, combinedProtocolAt_32, combinedDecZ] using
    combinedInj B p x msg decode 30 hr32 decision P Qtot hQ

#print axioms combinedInj31
#print axioms combinedInj32
end
end R0P.MaskDuplex

namespace R0P.Mask
open FS FS2 FS2.Duplex R0C.V3 R0P.SemSource R0P.SemD3Glue R0P.MaskDuplex AspisWideTower
open AspisV8R19.MemoizedProgramLaw AspisV8PairedCommitment
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
noncomputable section
variable {Sfield : Fin 29 → Subfield WideExact} {Pf : Type} {L : Nat}
variable (maskPoly : (Fin 10 → WideExact) → WideExact) (hMask : MaskDegree maskPoly)
variable (B : PackBasis (Sfield 0))
variable (p : Duplex.Params (MsgZ WideExact) (ChalZ WideExact) L)
variable (msg : Pf → Nat → MsgZ WideExact)
local notation "prZ" => combinedProtocolZ B p msg (fun _ _ => none)
local notation "VZ" => FS2.verifier (prZ) (combinedDecisionZ maskPoly B)

include hMask in
/-- Closed theorem43 instance. MaskDegree is the only mask-polynomial premise. -/
theorem combined_fiat_shamirZ (x : TypedContext WideExact Sfield) (hr32 : p.rounds = 32)
    (hσsem : ∀ (i : Nat) (_hi : i < 25) (s : State),
      p.σ i s = R0C.SemStatement.Chal.semantic (semChal s))
    (hσz0 : ∀ s : State, p.σ 25 s = R0C.SemStatement.Chal.circle (circleSample0 s))
    (hσz1 : ∀ s : State, p.σ 26 s = R0C.SemStatement.Chal.circle (circleSample1 s))
    (hσopen : ∀ (j : Fin 4) (s : State),
      p.σ (27+j.val) s = R0C.SemStatement.Chal.opening (R0C.V3.DQ.σQ j.val s))
    (P : Program (Addr L) State Pf) (Qtot : Nat)
    (hQ : ∀ H, FS2.distinctFirstReads (eval H (FS2.experiment P (VZ) x)) ≤ Qtot) :
    mean (fun H : Addr L → State =>
      indicator (FS2.accepts (eval H (FS2.experiment P (VZ) x)) ∧
        FS2.extractFails (prZ) x (eval H (FS2.experiment P (VZ) x)))) ≤
      (Qtot : ℚ) * maxErr combinedD2BudgetZ 32 + κ Qtot := by
  exact combined_fiat_shamir_of_obligations B p x msg (fun _ _ => none) 30 hr32
    (combinedDecisionZ maskPoly B) (duplexRowsZ maskPoly B combinedD2BudgetZ)
    (combinedD1Z maskPoly B p msg (fun _ _ => none) combinedD2BudgetZ)
    (combinedProtocolZ_D2 maskPoly B p msg (fun _ _ => none) hσsem hσz0 hσz1 hσopen)
    (d3Z AspisCircleGroupOrder.P semE_prime_eq maskPoly hMask B p msg (fun _ _ => none)
      combinedD2BudgetZ (hσopen 0)) P Qtot hQ

#print axioms combined_fiat_shamirZ
end
end R0P.Mask
