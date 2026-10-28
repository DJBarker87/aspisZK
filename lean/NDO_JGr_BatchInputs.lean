import NDO_JGr_PreBatchFixture
import NDO_JGr_Keys
import NDO_JGr_Counts
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGr_BatchInputs
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation FirstComposition JGr_Geometry

/-- Existing parameterised batch normalisation instantiated at the corrected
closed dictionary and THIS successful preparation. This is not batch success. -/
theorem batch_source (p : verifier.Prepared)
    (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (prepare : verifier.candidate.prepare installed digest (toCurrentPublic JFs_PublicSerialization.value)
      JFx_NativeBytes.proof () none input=ok (.Ok p,scratch)) :
    installed.op6 digest JFx_NativeBytes.proof p JGe_View.folded 0#usize ()=
      Op5T_Install.mapResult Op5T_Install.currentError
        (Op5T_Install.body Port4B_Install.leaves
          (⟨JGn_TerminalIdentified.shaDictionary.coremarkerCopyInst,digest.digest⟩ :
            AspisR1Stage2.aspis_core.digest.Digest32 Unit)
          JFx_NativeBytes.proof JFo_Prepared.value.queries JFo_Prepared.value.roots
          JGe_View.folded 0#usize ()) :=
  JGp_BatchInput.source JGp_Seeds.base (JFr_TX2_DotsBinding.ops JGp_Seeds.query)
    () JGp_Seeds.geometry JGn_TerminalIdentified.shaDictionary () p input scratch JGe_View.folded prepare
#print axioms batch_source

/-- Actual packed-key and sorting calls for THIS preparation's queries.
No native leaf, batch acceptance or successful verifier callback is assumed. -/
theorem source (p : verifier.Prepared)
    (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (prepare : verifier.candidate.prepare installed digest (toCurrentPublic JFs_PublicSerialization.value)
      JFx_NativeBytes.proof () none input=ok (.Ok p,scratch))
    (kind : Usize) (bound : kind.val<3) :
    Port4B_Install.leaves.op4 p.queries 0#usize 10#usize kind=ok (JGr_Keys.raw kind.val) ∧
    ∃ out : Array U64 16#usize,
      Port4B_Install.leaves.op5 (JGr_Keys.raw kind.val) 10#usize=ok out ∧
      Port4B_LeafLoop.KeyStream (Port4B_KeyInstall.queries p.queries) 0 kind.val out 0#usize
        (OraclePortFrozenOrder.sortedPositions (Port4B_KeyInstall.queries p.queries) 0 kind.val) := by
  have queries := JGp_CurrentQueries.source _ _ _ JGn_TerminalIdentified.shaDictionary () p input scratch prepare
  rw [queries]
  exact ⟨JGr_Keys.build kind bound,JGr_Keys.source kind.val⟩
#print axioms source

/-- Closed same-preparation non-vacuity of the builder and sorted-key stream.
This deliberately stops before leaf hashing and the native batch verifier. -/
theorem inhabited :
    ∃ (p : verifier.Prepared) (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize),
      verifier.candidate.prepare installed digest (toCurrentPublic JFs_PublicSerialization.value)
        JFx_NativeBytes.proof () none (Array.repeat 29#usize JGp_TX1Initial.zero)=ok (.Ok p,scratch) ∧
      ∀ (kind : Usize), kind.val<3 →
        Port4B_Install.leaves.op4 p.queries 0#usize 10#usize kind=ok (JGr_Keys.raw kind.val) ∧
        ∃ out : Array U64 16#usize,
          Port4B_Install.leaves.op5 (JGr_Keys.raw kind.val) 10#usize=ok out ∧
          Port4B_LeafLoop.KeyStream (Port4B_KeyInstall.queries p.queries) 0 kind.val out 0#usize
            (OraclePortFrozenOrder.sortedPositions (Port4B_KeyInstall.queries p.queries) 0 kind.val) := by
  obtain ⟨p,scratch,_initial,_pending,_g,prepare,_⟩ := JGr_Geometry.inhabited
  exact ⟨p,scratch,prepare,fun kind bound => source p _ scratch prepare kind bound⟩
#print axioms inhabited
end AspisR1.JGr_BatchInputs
end
