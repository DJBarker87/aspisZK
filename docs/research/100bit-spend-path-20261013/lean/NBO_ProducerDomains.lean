import NBO_WeightRead
import NBO_CircleDomain
set_option autoImplicit false
noncomputable section
namespace NBO_ProducerDomains
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2 Port3_NativeQueryBody
/-- Exact remaining upstream preparation projection on the SAME returned g. -/
structure Prepared (p : verifier.Prepared) (g : Array Stage2E 29#usize) : Prop where
 tail : NBO_AcceptedTail.PreparedDomain p
 alpha0 : NBO_TailDomain.WideCanonical (p.alpha.val[0]'(by rw [p.alpha.property];decide))
 powers : NBO_QueryDomains.AllWide g
/-- Exact named lower source-producer obligations. These quantify actual
child calls only; no query, flush, writer output or whole-body equality occurs. -/
structure NBA_NBC (base : VTop_Stages.Ops) (ops : Ops) : Prop where
 prepare : ∀ {Hash : Type} (D : VTop_Stages.aspis_core.digest.Digest32 Hash) hash
   semantic proof initial preparation g p,
   base.op7 D semantic proof hash none initial=ok (preparation,g) →
   core.result.Result.Insts.CoreOpsTry.branch preparation=ok (.Continue p) → Prepared p g
 geometry : ∀ queries split geometry,
   split.val=10 → base.op11 queries 0#usize split=ok (.Ok geometry) →
   NBO_QueryDomains.GeometryDomain geometry
 scanOpening : ∀ proof i q,
   base.op4 proof=ok (.Ok ()) → i.val<10 → ops.op11 proof i=ok q →
   NBO_CircleDomain.OpeningDomain q
/-- Existing writer-prefix producer hypotheses are exact projections of the
new explicit input laws; they are not extra independent witnesses. -/
theorem top (base : VTop_Stages.Ops) (ops : Ops) (laws : NBA_NBC base ops) :
 NBO_TopInstall.Producers base := by
 constructor
 · intro Hash D hash semantic proof initial preparation g p prep branch
   exact (laws.prepare D hash semantic proof initial preparation g p prep branch).tail
 · exact laws.geometry
#print axioms top
end NBO_ProducerDomains
end
