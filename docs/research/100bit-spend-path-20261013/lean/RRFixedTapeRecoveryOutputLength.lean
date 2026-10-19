import RRFixedTapeRecovery

set_option autoImplicit false

noncomputable section
namespace AspisR1.RRFixedTapeRecoveryOutputLength
open Polynomial CompPoly
open RRVectorRowPolynomialBridge
open AspisR1.RRFixedTapeRecovery
open AspisR1.RRConcreteState AspisR1.RRConcreteValidState
open AspisR1.RRConcreteInitialValidStateFromFacts
open AspisR1.RRConcreteStatePolynomialView
open AspisR1.RRConcreteTraversal AspisR1.RRConcreteTraversalLaw
open AspisR1.RRProgramTraversal AspisR1.RRProgramAbortBound
open AspisR1.RRProgramWalkRelation AspisR1.SequentialProgramInvariants
open AspisR1.SequentialFreshProgram
open AspisR1.SequentialFiniteTapeLaw AspisR1.RRConcreteRetryBudget
open AspisV8R19.OracleFiniteSupport
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K]

theorem terminal_zero_mass_pos [Fintype K] (ell : Nat) (s : ValidState ell K)
    (hz : zeroTest s.val = true) : 1 ≤ mass ell s := by
  have hmodel0 : (model s.val).eval 0 = 0 := (zeroTest_exact s.val).mp hz
  have hcolumn : zeroColumnPolynomial s.val = 0 := by
    have hz' : zeroColumnPolynomial s.val == 0 := by
      simpa [zeroTest] using hz
    exact beq_iff_eq.mp hz'
  have hconstant : ((model s.val).eval 0).coeff 0 = 0 := by
    rw [← zeroColumn_toPoly s.val]
    have hzero := congrArg (fun p : CPolynomial K => p.toPoly) hcolumn
    have hcoeff := congrArg (fun p : K[X] => p.coeff 0) hzero
    simpa only [CPolynomial.toPoly_zero, Polynomial.coeff_zero] using hcoeff
  have hcoeffMap :
      ((model s.val).map (Polynomial.evalRingHom (0 : K))).coeff 0 =
        ((model s.val).eval 0).coeff 0 := by
    rw [Polynomial.coeff_map]
    simp only [Polynomial.coe_evalRingHom]
    rw [(Polynomial.coeff_zero_eq_eval_zero (p := model s.val)).symm]
    exact (Polynomial.coeff_zero_eq_eval_zero _).symm
  have hcoeffMapEval :
      Polynomial.evalRingHom (0 : K) ((model s.val).coeff 0) =
        ((model s.val).eval 0).coeff 0 := by
    simpa only [Polynomial.coeff_map] using hcoeffMap
  have hscalar : (scalarPolynomial s.val).toPoly =
      (model s.val).map (Polynomial.evalRingHom (0 : K)) := by
    rw [scalarPolynomial_toPoly, model_specialization]
  have hp : (scalarPolynomial s.val).toPoly ≠ 0 := scalar_nonzero ell s
  have hcoeff : (scalarPolynomial s.val).toPoly.coeff 0 = 0 := by
    rw [hscalar, Polynomial.coeff_map, hcoeffMapEval, hconstant]
  have hdiv : Polynomial.X ∣ (scalarPolynomial s.val).toPoly :=
    Polynomial.X_dvd_iff.mpr hcoeff
  have hdeg := Polynomial.natDegree_le_of_dvd hdiv hp
  rw [← CPolynomial.natDegree_toPoly] at hdeg
  simpa [mass] using hdeg

theorem walkResult_length_le {S : Type} {P : S → List (List K) → Prop}
    {mass : S → Nat} {cs : List (K × S)} {ys : List (List K)}
    (hw : WalkResult P cs ys)
    (hP : ∀ s ys, P s ys → ys.length ≤ mass s) :
    ys.length ≤ childMass mass cs := by
  induction hw with
  | nil => simp [childMass]
  | cons a s tail ys zs hhead htail ih =>
      simp only [List.length_append, List.length_map, childMass,
        List.map_cons, List.sum_cons]
      exact Nat.add_le_add (hP s ys hhead) ih

theorem collectProgram_output_length_le
    {I A S : Type} [Fintype A] [Nonempty A]
    (zeroTest : S → Bool)
    (children : S → Program I A (Option (List (K × S))))
    (mass : S → Nat)
    (hbase : ∀ s, zeroTest s = true → 1 ≤ mass s)
    (hmass : ∀ s, AllOutcomes (children s) (fun out =>
      ∀ cs, out = some cs → childMass mass cs ≤ mass s))
    (d : Nat) (s : S) :
    AllOutcomes (collectProgram zeroTest children d s)
      (fun out => ∀ ys, out = some ys → ys.length ≤ mass s) := by
  induction d generalizing s with
  | zero =>
      intro ys hys
      by_cases hz : zeroTest s = true
      · simp only [collectProgram, hz, ↓reduceIte, Option.some.injEq] at hys
        subst ys
        simpa using hbase s hz
      · simp only [collectProgram, hz, ↓reduceIte, Option.some.injEq] at hys
        subst ys
        exact Nat.zero_le _
  | succ d ih =>
      change AllOutcomes
        (optionBind (children s)
          (walkChildren (collectProgram zeroTest children d)))
        (fun out => ∀ ys, out = some ys → ys.length ≤ mass s)
      apply all_bind
      apply all_mono _ (hmass s)
      intro head hhead
      cases head with
      | none =>
          intro ys hys
          cases hys
      | some cs =>
          have hcs := hhead cs rfl
          have hwalk := walkChildren_all
            (collectProgram zeroTest children d)
            (fun u ys => ys.length ≤ mass u)
            (fun u => ih u) cs
          apply all_mono _ hwalk
          intro out hout ys hys
          have hlen := walkResult_length_le (hout ys hys)
            (fun u zs hz => hz)
          have hbound : childMass mass cs ≤ mass s := hcs
          exact hlen.trans hbound

theorem run_output_length_le [Fintype K]
    (ell q t d : Nat) (s : ValidState ell K) (hq : q = Fintype.card K) :
    AllOutcomes (run ell q t d s)
      (fun out => ∀ ys, out = some ys → ys.length ≤ mass ell s) := by
  unfold run
  apply collectProgram_output_length_le
    (fun u : ValidState ell K => zeroTest u.val)
    (fun u => children ell u q t) (mass ell)
  · intro u hu
    have h := terminal_zero_mass_pos ell u hu
    exact h
  · intro u
    exact children_mass ell u q t hq

theorem recover_output_length_le [Fintype K]
    (ell q t d : Nat) (s : RawState K)
    (hd : ∀ i ≤ s.maxX, (inputPolynomial s.rows i).natDegree ≤ ell)
    (hn : model s ≠ 0) (hq : q = Fintype.card K)
    (H : {i : Nat // i ∈ Finset.range (d * ell)} → Fin t → K × K)
    (candidates : List (List K))
    (hs : (recover ell q t d s hd hn H).1 = some candidates) :
    candidates.length ≤ ell := by
  let initial := initialValidState ell s hd hn
  have hall := run_output_length_le ell q t d initial hq
  have hseq := all_sequential (run ell q t d initial) _ hall 0
  have heval := all_eval
    (extend (Finset.range (d * ell)) H (fun _ => (0, 0)))
    (sequential (run ell q t d initial) 0) _ hseq
  have hmass : mass ell initial ≤ ell := mass_le_ell ell initial
  unfold recover at hs
  exact (heval candidates hs).trans hmass

#print axioms terminal_zero_mass_pos
#print axioms walkResult_length_le
#print axioms collectProgram_output_length_le
#print axioms run_output_length_le
#print axioms recover_output_length_le
end AspisR1.RRFixedTapeRecoveryOutputLength
end
