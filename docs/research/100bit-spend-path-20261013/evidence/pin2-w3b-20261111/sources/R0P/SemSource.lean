import R0C.SemStatement
import R0P.Semantics

/-! Lead: the pair-forest instance of the B2 semantic extension, part 1.

`R0C.SemStatement.SourceData` was left as open data in the close job. The
fields fixed by the SEM work are supplied here: the public context carries
the pair-forest public input and the committed words; the payment witness
is `InputNoteExtracted` for a candidate trace of the committed words. The
round classifier `semanticBad` (24 rounds, G13′) and `openingView` are the
remaining data; D1 is proved for every `SourceData` from the definition of
`doomed` at the empty prefix. -/
set_option autoImplicit false
namespace R0P.SemSource
open FS FS2 R0C.SemStatement
open AspisPool.AlgorithmicCircleDecoderV7 AspisV8R19.MemoizedProgramLaw
open AspisV8R19.OracleProgramOps AspisV8R19.AdaptiveFirstReadLaw
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound AspisV8PairedCommitment

noncomputable section
attribute [local instance] Classical.propDecidable

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {Sfield : Fin 29 → Subfield K}

/-- The public initial context: the pair-forest public input and the
committed words (whose candidate list `Lambda W` the semantic rounds
quantify over). -/
structure Context (K : Type) [Field K] where
  pub : Public K
  W : Fin 29 → InitialWord K

/-- The payment witness: a candidate trace with an extracted input note. -/
def paymentWitness (x : Context K) (t : Trace K) : Prop := InputNoteExtracted x.pub t

/-- D1 for every semantic `SourceData`: no witness means doomed at the empty
prefix, since no round has been played. -/
theorem d1_of_sourceData {X SM W Pf I A : Type} [DecidableEq I] [Inhabited A] [Fintype A]
    (s : SourceData (K := K) (E := K) X SM W Sfield)
    (msg : Pf → Nat → Msg K K SM)
    (samp : Nat → Prefix K K X SM → Msg K K SM → FS2.Sampler I A (Chal K K))
    (decode : I → Table I A →
      Option (FS2.Sampler I A (Prefix K K X SM × Msg K K SM × Chal K K))) :
    FS2.D1 (protocol s msg samp decode) (stateRows s) := by
  intro x T hx
  refine ⟨?_, ?_⟩
  · intro hw
    change R0C.SemStatement.extract s x T = none at hx
    unfold R0C.SemStatement.extract at hx
    split at hx
    · exact Option.some_ne_none _ hx
    · rename_i hno
      exact (hno hw).elim
  · intro h
    exact h

#print axioms d1_of_sourceData
end
end R0P.SemSource
