import RRConcreteValidState
import RRProgramRecoveryContracts
import RRProgramSequentialContract
import RRProgramQueryBound
import RRReturnedRootMass

namespace AspisR1.RRConcreteTraversal
open CompPoly AspisR1.RRConcreteState AspisR1.RRConcreteValidState
open AspisR1.CompPolyGeneralRootsProgram
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K]

def children (ell : Nat) (s : ValidState ell K) (q t : Nat) :
    Program Nat (Fin t → K × K) (Option (List (K × ValidState ell K))) :=
  bind (generalRootsProgram (scalarPolynomial s.val) q t)
    (fun out => .done (out.1.map (fun roots => roots.map (fun a => (a, child ell s a)))))

def run (ell q t d : Nat) (s : ValidState ell K) :
    Program Nat (Fin t → K × K) (Option (List (List K))) :=
  AspisR1.RRProgramTraversal.collectProgram (fun s => zeroTest s.val)
    (fun s => children ell s q t) d s

def mass (ell : Nat) (s : ValidState ell K) : Nat :=
  (scalarPolynomial s.val).natDegree

noncomputable section
open Polynomial RRRootDescent
open AspisR1.SequentialProgramInvariants AspisR1.CompPolySequentialRootsContract
open AspisR1.RRProgramRecoveryContracts AspisR1.RRProgramAbortBound
open AspisR1.RRReturnedRootMass AspisR1.RRConcreteStatePolynomialView
open AspisR1.CompPolyFactorMeanTools AspisR1.ProgramQueryCost
variable [Fintype K]

theorem scalar_nonzero (ell : Nat) (s : ValidState ell K) :
    (scalarPolynomial s.val).toPoly ≠ 0 := by
  rw [scalarPolynomial_toPoly]
  exact s.property.1

theorem children_roots (ell : Nat) (s : ValidState ell K) (q t : Nat)
    (hq : q = Fintype.card K) :
    AllOutcomes (children ell s q t) (fun output => ∀ cs, output = some cs →
      ∃ roots : List K, cs = roots.map (fun a => (a, child ell s a)) ∧
        (∀ a, IsRoot (scalarPolynomial s.val).toPoly a ↔ a ∈ roots) ∧ roots.Nodup) := by
  unfold children
  apply all_bind
  apply all_mono _ (generalRoots_correct (scalarPolynomial s.val) q t hq (scalar_nonzero ell s))
  intro sampled hs
  change ∀ cs, sampled.1.map _ = some cs → _
  intro cs hcs
  cases hroots : sampled.1 with
  | none => simp [hroots] at hcs
  | some roots =>
    have hc := hs.2 roots hroots
    have he : roots.map (fun a => (a, child ell s a)) = cs := by
      simpa only [hroots, Option.map_some, Option.some.injEq] using hcs
    exact ⟨roots, he.symm, hc.1, hc.2.1⟩

theorem children_mass (ell : Nat) (s : ValidState ell K) (q t : Nat)
    (hq : q = Fintype.card K) :
    AllOutcomes (children ell s q t) (fun out => ∀ cs, out = some cs →
      childMass (mass ell) cs ≤ mass ell s) := by
  apply all_mono _ (children_roots ell s q t hq)
  intro out ho cs hcs
  obtain ⟨roots,rfl,hroots,hn⟩ := ho cs hcs
  have hb := root_list_mass_le_degree (scalarPolynomial s.val).toPoly
    (scalar_nonzero ell s) roots hn (fun a ha => (hroots a).mpr ha)
    (fun a => mass ell (child ell s a)) (fun a _ => by
      simpa only [mass, CPolynomial.natDegree_toPoly] using child_scalar_degree_le ell s a)
  simpa only [childMass, List.map_map, Function.comp_def, mass,
    CPolynomial.natDegree_toPoly] using hb

theorem children_recovery (ell : Nat) (s : ValidState ell K) (q t : Nat)
    (hq : q = Fintype.card K) :
    AllOutcomes (children ell s q t) (fun out => ∀ cs, out = some cs →
      (∀ a u, (a,u) ∈ cs → ∀ f,
        (model u.val).eval f = 0 → (model s.val).eval (C a + X*f) = 0) ∧
      (∀ f, (model s.val).eval f = 0 → ∃ a u, (a,u) ∈ cs ∧
        a = f.coeff 0 ∧ (model u.val).eval f.divX = 0)) := by
  apply all_mono _ (children_roots ell s q t hq)
  intro out ho cs hcs
  obtain ⟨roots,rfl,hroots,hn⟩ := ho cs hcs
  constructor
  · intro a u hmem f hf
    obtain ⟨b,hb,he⟩ := List.mem_map.mp hmem
    cases he
    exact (child_model_roots ell s a f).mp hf
  · intro f hf
    let a := f.coeff 0
    have ha : IsRoot (scalarPolynomial s.val).toPoly a := by
      rw [scalarPolynomial_toPoly, ← model_specialization]
      change ((model s.val).map (Polynomial.evalRingHom (0 : K))).eval a = 0
      simpa only [a, ← Polynomial.coeff_zero_eq_eval_zero] using
        constant_coefficient_is_root (model s.val) f hf
    refine ⟨a,child ell s a,List.mem_map.mpr ⟨a,(hroots a).mp ha,rfl⟩,rfl,?_⟩
    apply (child_model_roots ell s a f.divX).mpr
    simpa only [a, head_tail] using hf

/-- Soundness and completeness now hold for the actual scalar root program,
actual finite scanner, actual runtime row child, and executable terminal test.
No abstract hzero/hchildren contract is a premise. -/
theorem run_recovery (ell q t d : Nat) (s : ValidState ell K)
    (hq : q = Fintype.card K) :
    AllOutcomes (run ell q t d s) (fun out => ∀ candidates, out = some candidates →
      CandidateResult (fun u : ValidState ell K => model u.val) d s candidates) := by
  exact collectProgram_correct (fun s => zeroTest s.val) (fun s => children ell s q t)
    (fun s => model s.val) (fun s => zeroTest_exact s.val)
    (fun s => children_recovery ell s q t hq) d s

#print axioms children
#print axioms run
#print axioms mass
#print axioms scalar_nonzero
#print axioms children_roots
#print axioms children_mass
#print axioms children_recovery
#print axioms run_recovery
end
end AspisR1.RRConcreteTraversal
