import S9ConstructorV3SuccessorCarryBodyCanonicalV1
import S9ConstructorV3QMMulSemanticsV1
import S9ConstructorV3QMAddSubSemanticsV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1S9ConstructorV3CarryBodySemanticsV1
open AspisR1S9ConstructorV3Loop2InnerCanonicalV1
open AspisR1S9ConstructorV3SuccessorCarryBodyCanonicalV1
abbrev Can := AspisR1S9ConstructorV3QMMulSemanticsV1.Can
abbrev decode := AspisR1S9ConstructorV3QMMulSemanticsV1.decode

/-- Exact field meaning of this SAME successful source carry step. All arithmetic
witnesses come from execution inversion; no child-call equation is assumed. -/
theorem carry_body_success_exact
    (z successor successorOut : Vector) (iter iterNext : ReverseRange)
    (carry carryOut : Q) (hz : VectorCanonical z) (hc : Can carry)
    (hbody : AspisR1S9ActualWeightsNewBoxNewV3.state_only_prefix.state_only_statement_points_loop.body
      z iter successor carry = .ok (.cont (iterNext,successorOut,carryOut))) :
    ∃ (coordinate : Usize) (bit cell : Q),
      core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
        (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize) iter =
          .ok (some coordinate,iterNext) ∧
      Array.index_usize z coordinate = .ok bit ∧
      Array.update successor coordinate cell = .ok successorOut ∧
      Can carryOut ∧ Can cell ∧
      decode carryOut = decode bit * decode carry ∧
      decode cell = decode bit + decode carry -
        (decode bit * decode carry + decode bit * decode carry) := by
  obtain ⟨coordinate,bit,product,sum,twice,cell,hnext,hbit,hm,ha,ht,hs,hu,he⟩ :=
    carry_body_success_has_execution z successor successorOut iter iterNext carry carryOut hbody
  have hb : Can bit := raw_read_canonical z coordinate bit hz hbit
  obtain ⟨hpc,hpm⟩ := AspisR1S9ConstructorV3QMMulSemanticsV1.generated_mul_success_exact
    bit carry product hb hc hm
  obtain ⟨hsc,hsm⟩ := AspisR1S9ConstructorV3QMAddSubSemanticsV1.generated_add_success_exact
    bit carry sum hb hc ha
  obtain ⟨htc,htm⟩ := AspisR1S9ConstructorV3QMAddSubSemanticsV1.generated_add_success_exact
    product product twice hpc hpc ht
  obtain ⟨hcc,hcm⟩ := AspisR1S9ConstructorV3QMAddSubSemanticsV1.generated_sub_success_exact
    sum twice cell hsc htc hs
  change decode product=decode bit*decode carry at hpm
  change decode sum=decode bit+decode carry at hsm
  change decode twice=decode product+decode product at htm
  change decode cell=decode sum-decode twice at hcm
  subst carryOut
  refine ⟨coordinate,bit,cell,hnext,hbit,hu,hpc,hcc,hpm,?_⟩
  rw [hcm,hsm,htm,hpm]

#print axioms carry_body_success_exact
end AspisR1S9ConstructorV3CarryBodySemanticsV1
