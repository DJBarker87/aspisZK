import NLI_RoundsCarry
import NLI_ParsedCase
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLI_RoundsInstall
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NJG_RoundsCode
open PreparedHashCode (run)
/-- Invoke the authoritative CLOSED134 root itself at the SAME input. Its
complete child-domain family and source hash frame are retained, not assumed.
The parent cut here covers return ABI only; full136 input/heap composition
remains a separate obligation. -/
theorem source {H : Type} (native : NLI_RoundsCarry.Native) (cut : NLI_RoundsCarry.Cut native)
 (childNative : NJM_RoundsCut.Observations) (childCut : NJM_RoundsCut.Cut childNative)
 (token frame : Nat) (D : aspis_core.Digest32 H) (bytes : Slice U8)
 (pre : AspisR1PrefixAggregateParser.r1_wire.Prefix)
 (parsed : AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes=ok (.Ok pre))
 (before : r1_wire.SemanticTranscript H) :
 (∃ running,NLI_RoundsCarry.afterChild native before.hash
  (NJM_RoundsInduction.chain childNative token frame D (PrefixAdapter.fromOld pre) sites
   (running,Array.repeat 10#usize aspis_core.field.QM31.ZERO,before))=
  run (S1SemanticCode.rounds NJM_RoundJoin.R D (PrefixAdapter.fromOld pre) before)) ∧
 (∀ (r : Usize) (member : r∈sites) (carry : Carry H),
  NJM_RoundsClosed.Child D bytes pre parsed carry.2.2 carry.2.1 carry.1 r (sites_domain r member)) ∧
 NLI_RoundsHash.Outcome before.hash (run (S1SemanticCode.rounds NJM_RoundJoin.R D (PrefixAdapter.fromOld pre) before)).2 := by
 have packet:=NJM_InvocationRoots.rounds childNative childCut token frame D bytes before
 have accepted:=NLI_ParsedCase.success _ _ packet pre parsed
 rcases accepted with ⟨⟨running,whole⟩,domains⟩
 refine ⟨⟨running,?_⟩,domains,NLI_RoundsHash.source D bytes pre parsed before⟩
 rw [←whole]
 exact NLI_RoundsCarry.source native cut D bytes pre parsed before
#print axioms source
#print source
end AspisR1.NLI_RoundsInstall
end
