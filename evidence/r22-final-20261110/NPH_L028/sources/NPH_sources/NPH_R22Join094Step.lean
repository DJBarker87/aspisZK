import NPH_R22Join094
import NFS_CallerDomains
import NFS_AccumDomain

/-! NPH_ (R22, step 3): the composed value flow of one tx1 query_values step on the
installed library dictionary Dsel = NFS_CallerDomains.ops LIBC_QueryOps.seed.
From the tx1 packet Domain alone (NOC_QueryDomain.domain produces it at 094):
- the four opening values returned by op0/op21 are canonical (NFS_CallerDomains.fields);
- the four dots returned by op20 are canonical (NFS_CallerDomains.dots, on the Domain's
  canonical g);
- the circle call op17(alpha[0], dots, ·) and the line call op16(alpha[1], values, ·) are ok
  with canonical outputs, so every CurrentWide kernel call inside them has W arguments;
- the line output is the accumulate value, WideCanonical (NFS_AccumDomain.line), so the
  three accumulate tail calls op3/op2/op9 (SelectedMaskProbe QM31 tower through
  NBO_FieldSemantics) are ok on canonical arguments;
- the node computation on line_z (op7/op8/op5/op6) is ok for every input.
NOC_QueryLink.values_eq makes the installed dictionary Dcon agree with Dsel on every reached
query_values step. Standard axioms; nothing merged is changed. -/
set_option autoImplicit false
namespace AspisR1.NPH_R22Join094Step
open Aeneas Aeneas.Std Result AspisR1.NPH_R22Join094

theorem query_step_sites {proof p g geo start finish a b}
    (d : AspisR1.NFS_PacketRoot.Domain proof p g geo start finish a b)
    (q : Slice U8) (values : Array SAQ_WideABI.E 4#usize)
    (runValues : Dsel.op0 4#usize
      (Port3_NativeQueryBody.verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact Dsel) q = ok values)
    (dots : Array SAQ_WideABI.E 4#usize) (qPlace gPlace : Nat)
    (runDots : FIp_DotsAdapter.dots q g = ok dots)
    (we4 we6 : SAQ_WideABI.E) (h0 : Array.index_usize p.alpha 0#usize = ok we4)
    (h1 : Array.index_usize p.alpha 1#usize = ok we6) (inverse : Array U32 5#usize) :
    (∃ folded, Dsel.op17 we4 dots inverse = ok folded ∧ Port4C_QueryArithmetic.CanonE folded) ∧
    ∃ folded1, Dsel.op16 we6 values inverse = ok folded1 ∧
      ∃ we we1 q', Dsel.op3 folded1 a.power = ok we ∧ NBO_TailDomain.WideCanonical we ∧
        Dsel.op2 a.rhs we = ok we1 ∧ NBO_TailDomain.WideCanonical we1 ∧
        Dsel.op9 a.power p.rho = ok q' ∧ NBF_PowerStep.Canonical q' := by
  have cv := AspisR1.NFS_CallerDomains.fields LIBC_QueryOps.seed q values runValues
  have cd := AspisR1.NFS_CallerDomains.dots q g qPlace gPlace d.gCanonical dots runDots
  have ca := alpha_sites d
  refine ⟨circle_site we4 dots inverse (ca.1 we4 h0) cd, ?_⟩
  obtain ⟨folded1, hl, _⟩ := line_site we6 values inverse (ca.2 we6 h1) cv
  have wc := AspisR1.NFS_AccumDomain.line we6 values inverse folded1 hl
  exact ⟨folded1, hl, tail_sites d.invariant folded1 wc⟩

#print axioms query_step_sites
end AspisR1.NPH_R22Join094Step
