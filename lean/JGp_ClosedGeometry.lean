import JGp_Seeds
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGp_ClosedGeometry
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation FirstComposition

def installed : Ops := JGp_TX1Geometry.ops JGp_Seeds.base JGp_Seeds.query () JGp_Seeds.geometry
def digest : aspis_core.digest.Digest32 Unit :=
  F3V_OracleDictionary.current JFp_SHADigest.digest JGn_TerminalIdentified.shaDictionary

/-- Closed local non-vacuity, with all seed dictionaries inhabited. This is
not accepted1, a writer return, an accepted pair or the deployed fixture. -/
theorem inhabited :
    ∃ (p : verifier.Prepared) (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
      (initial : verifier.Accumulator) (pending : verifier.BatchedWeights) (g : verifier.QueryGeometry),
      verifier.candidate.prepare installed digest (toCurrentPublic JFs_PublicSerialization.value)
        JFx_NativeBytes.proof () none (Array.repeat 29#usize JGp_TX1Initial.zero)=ok (.Ok p,scratch) ∧
      p.queries=JFq_Queries.value ∧ installed.op20 .S2=ok (.Ok initial) ∧
      installed.op18 initial.weights.deref=ok (.Ok pending) ∧
      installed.op19 p.queries 0#usize 10#usize=ok (.Ok g) ∧
      JGp_Loop.Meaning (Tx1Q_Carriers.geometry g) ∧
      verifier.candidate.tx1 installed digest (toCurrentPublic JFs_PublicSerialization.value)
        JFx_NativeBytes.publicInput JFx_NativeBytes.proof 10#usize () none=
        Tx1Reachability.afterPrepare installed digest JFx_NativeBytes.publicInput JFx_NativeBytes.proof
          10#usize () none p scratch :=
  JGp_TX1Geometry.inhabited JGp_Seeds.base JGp_Seeds.query () JGp_Seeds.geometry JGn_TerminalIdentified.shaDictionary ()
#print axioms inhabited
end AspisR1.JGp_ClosedGeometry
end
