import R0P.SemDuplexDensity
import R0P.SemDuplexDecodes
import R0P.SemCharP

/-! The theorem43 instance for the combined 31-round protocol.
The error schedule is kept as maxErr combinedD2Budget 31; its closed form
belongs to the separate accounting step. -/
set_option autoImplicit false
namespace R0P.SemDuplex
open FS FS2 FS2.Duplex R0C.V3 R0P R0P.SemSource R0P.SemD3Glue
open AspisV8R19.MemoizedProgramLaw AspisV8PairedCommitment
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
noncomputable section
variable {Sfield : Fin 29 → Subfield SemE} {Pf : Type} {L : Nat}
variable (B : PackBasis (Sfield 0))
variable (p : Duplex.Params CM (R0C.SemStatement.Chal SemE SemE) L)
variable (msg : Pf → Nat → CM)

/-- Every combined challenge round starts with its absorb cell. -/
theorem combinedChainsRead (decode : CombinedDecode Sfield L) :
    ChainsRead (combinedProtocol B p msg decode) := by
  intro i P m _
  show firstCell (combinedSampler p i P m) ≠ none
  unfold combinedSampler
  split <;> simp [firstCell, Duplex.samp]

/-- The verifier reads the first cell of each challenge chain. -/
theorem combinedReadsChains (decode : CombinedDecode Sfield L) :
    ReadsChains (combinedProtocol B p msg decode)
      (FS2.verifier (combinedProtocol B p msg decode) (combinedDecision B)) := by
  intro H x π j a hj ha
  exact FS2.verifier_reads (combinedProtocol B p msg decode) (combinedDecision B)
    H x π j hj a (R0C.V3.DQ.firstCell_mem H _ a ha)

/-- Extraction failure implies the initial source prefix is doomed. -/
theorem combinedD1 (decode : CombinedDecode Sfield L) (budget : Nat → ℚ) :
    FS2.D1 (combinedProtocol B p msg decode) (duplexRows B budget) := by
  intro x T hx
  change R0C.SemStatement.extract (sourceData B) x T = none at hx
  change (¬ ∃ w, (sourceData B).paymentWitness x w) ∧
    ¬ R0C.SemStatement.hitFrom (sourceData B) x [] []
  constructor
  · intro hw
    rw [R0C.SemStatement.extract, dif_pos hw] at hx
    cases hx
  · exact fun h => h

#print axioms combinedChainsRead
#print axioms combinedReadsChains
#print axioms combinedD1

local notation "prC" => combinedProtocol B p msg (fun _ _ => none)
local notation "VC" => FS2.verifier (prC) (combinedDecision B)

/-- The combined semantic/circle/opening protocol instantiated in theorem43.
The unused FS2 decoder field is none; the v3 completing decoder supplies Inj3. -/
theorem combined_fiat_shamir (x : CX Sfield) (hr31 : p.rounds = 31)
    (hσsem : ∀ (i : Nat) (_hi : i < 24) (s : State),
      p.σ i s = R0C.SemStatement.Chal.semantic (semChal s))
    (hσz0 : ∀ s : State, p.σ 24 s = R0C.SemStatement.Chal.circle (circleSample0 s))
    (hσz1 : ∀ s : State, p.σ 25 s = R0C.SemStatement.Chal.circle (circleSample1 s))
    (hσopen : ∀ (j : Fin 4) (s : State),
      p.σ (26 + j.val) s = R0C.SemStatement.Chal.opening (R0C.V3.DQ.σQ j.val s))
    (P : Program (Addr L) State Pf) (Qtot : Nat)
    (hQ : ∀ H, FS2.distinctFirstReads (eval H (FS2.experiment P (VC) x)) ≤ Qtot) :
    mean (fun H : Addr L → State =>
        indicator (FS2.accepts (eval H (FS2.experiment P (VC) x)) ∧
          FS2.extractFails (prC) x (eval H (FS2.experiment P (VC) x)))) ≤
      (Qtot : ℚ) * maxErr combinedD2Budget 31 + κ Qtot := by
  have hσ26 : ∀ s, p.σ 26 s = R0C.SemStatement.Chal.opening (R0C.V3.DQ.σQ 0 s) :=
    hσopen 0
  exact R0C.V3.theorem43 (prC) (duplexRows B combinedD2Budget) (combinedDec p B x)
    P (VC) x κ Qtot
    (combinedD1 B p msg (fun _ _ => none) combinedD2Budget)
    (combinedChainDensity B p x msg (fun _ _ => none) hr31 hσsem hσz0 hσz1 hσopen)
    (R0P.SemD3Glue.d3 AspisCircleGroupOrder.P semE_prime_eq B p msg (fun _ _ => none)
      combinedD2Budget hσ26)
    (combinedChainsRead B p msg (fun _ _ => none))
    (combinedReadsChains B p msg (fun _ _ => none))
    { Coll := Coll p Qtot
      mass := coll_mass p Qtot P (VC) x hQ
      decodes := fun H hc i a hi ha => combinedDecodes B p x msg (fun _ _ => none)
        hr31 (combinedDecision B) P Qtot hQ H hc i a hi ha }
    hQ

#print axioms combined_fiat_shamir
end
end R0P.SemDuplex
