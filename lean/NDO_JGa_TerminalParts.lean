import RPv_JGa_ActiveLoop
import RPv_JGa_ActiveMaskKinds
import RPv_JGa_ActiveMasks
import RPv_JGa_ArrayProperty
import NDO_JGa_Audit
import NDO_JGa_ChallengeCanonical
import RPv_JGa_Copy
import RPv_JGa_CopyEndpoint
import NDO_JGa_CopyFixture
import RPv_JGa_CopyLoop
import RPv_JGa_CopyPatterns
import RPv_JGa_CopyPowers
import NDO_JGa_DigestLane
import NDO_JGa_DigestLoop
import NDO_JGa_DigestTarget
import NDO_JGa_EmptyRoot
import NDO_JGa_Equality
import NDO_JGa_EqualityCell
import NDO_JGa_EqualityLoop
import NDO_JGa_Fixture
import NDO_JGa_FrontierLoop
import NDO_JGa_FrontierStep
import RPv_JGa_LinkBounds
import RPv_JGa_LinkChunk00
import RPv_JGa_LinkChunk01
import RPv_JGa_LinkChunk02
import RPv_JGa_LinkChunk03
import RPv_JGa_LinkChunk04
import RPv_JGa_LinkChunk05
import RPv_JGa_LinkChunk06
import RPv_JGa_LinkChunk07
import RPv_JGa_LinkShape
import RPv_JGa_LinkWeight
import RPv_JGa_LinkWeightBits
import RPv_JGa_LinkWeightSimple
import NDO_JGa_Map
import RPv_JGa_MaskLoops
import RPv_JGa_MaskStep
import RPv_JGa_PatternBounds
import RPv_JGa_PatternCell
import RPv_JGa_PatternInner
import RPv_JGa_PatternOuter
import NDO_JGa_PublicDigest
import NDO_JGa_PublicDigestPrefix
import NDO_JGa_PublicDigestSuffix
import NDO_JGa_Reconstruct
import NDO_JGa_Semantic
import NDO_JGa_SemanticTail
import NDO_JGa_ValueBitsSpecs
import NDO_JGa_ValueConservation
import NDO_JGa_ValueFinish
import NDO_JGa_ValueLanes
import NDO_JGa_ValueScale
import NDO_JGa_ValueSelectors
import NDO_JGa_ValueTail
import RPv_JGa_WeightShift
import RPv_FJa_PoseidonLowOnRun
import RPv_FJa_PoseidonPow5
import NDO_JGa_Equality
import RPv_JFy_Steps
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGa_TerminalParts
open Aeneas Aeneas.Std Result WP FIq_Native
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
open pool_v1.pair_forest_semantic_terminal

/-- Forward terminal arithmetic, conditional on the explicitly supplied SAME composition return.
This is not a real-byte composition or terminal-acceptance instance. -/
theorem source (p : SemanticPublic) (claims : Array field.QM31 84#usize)
    (point zc : Array field.QM31 10#usize) (lambda chi theta mu : field.QM31)
    (comp : field.QM31) (c1 : Array field.QM31 16#usize) (mask : Array field.QM31 10#usize)
    (g h1 active : field.QM31)
    (hcomp : composition_parts p claims point lambda chi theta=ok (.Ok (comp,c1,mask,g,h1,active)))
    (hp : canonical point) (hz : canonical zc) (hc : Canon comp) (hm : Canon mu)
    (hh : Canon h1) (ha : Canon active) :
    ∃ out,terminal_parts p claims point lambda chi theta zc mu=ok (.Ok (out,c1,mask,g)) ∧ Canon out := by
  obtain ⟨eq,heq,heqc,_⟩ := JGa_Equality.source zc point hz hp
  have one := FIv_NativeValue.one.1
  have spec : terminal_parts p claims point lambda chi theta zc mu
      ⦃ out => ∃ q,out=.Ok (q,c1,mask,g) ∧ Canon q ⦄ := by
    unfold terminal_parts
    rw [hcomp,bind_tc_ok]
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,Aeneas.Std.uncurry]
    rw [heq,bind_tc_ok]
    step*
  obtain ⟨result,call,q,same,hq⟩ := WP.spec_imp_exists spec
  exact ⟨q,same ▸ call,hq⟩
#print axioms source
end AspisR1.JGa_TerminalParts
end

#print AspisR1.Rc7_Top.deployed
#print axioms AspisR1.Rc7_Top.deployed
#print AspisR1.Rc10_Top.deployed
#print axioms AspisR1.Rc10_Top.deployed
#print AspisR1.JGa_Fixture.inhabited
#print axioms AspisR1.JGa_Fixture.inhabited
#print AspisR1.JGa_CopyFixture.inhabited
#print axioms AspisR1.JGa_CopyFixture.inhabited
#print axioms AspisR1.JGa_Semantic.source
#print axioms AspisR1.JGa_Copy.source
#print axioms AspisR1.JGa_Equality.source
#print axioms AspisR1.FJa_PoseidonLowOnRun.value
#print axioms AspisR1.FJa_PoseidonPow5.value
