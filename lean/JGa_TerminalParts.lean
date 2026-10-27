import JGa_ActiveLoop
import JGa_ActiveMaskKinds
import JGa_ActiveMasks
import JGa_ArrayProperty
import JGa_Audit
import JGa_ChallengeCanonical
import JGa_Copy
import JGa_CopyEndpoint
import JGa_CopyFixture
import JGa_CopyLoop
import JGa_CopyPatterns
import JGa_CopyPowers
import JGa_DigestLane
import JGa_DigestLoop
import JGa_DigestTarget
import JGa_EmptyRoot
import JGa_Equality
import JGa_EqualityCell
import JGa_EqualityLoop
import JGa_Fixture
import JGa_FrontierLoop
import JGa_FrontierStep
import JGa_LinkBounds
import JGa_LinkChunk00
import JGa_LinkChunk01
import JGa_LinkChunk02
import JGa_LinkChunk03
import JGa_LinkChunk04
import JGa_LinkChunk05
import JGa_LinkChunk06
import JGa_LinkChunk07
import JGa_LinkShape
import JGa_LinkWeight
import JGa_LinkWeightBits
import JGa_LinkWeightSimple
import JGa_Map
import JGa_MaskLoops
import JGa_MaskStep
import JGa_PatternBounds
import JGa_PatternCell
import JGa_PatternInner
import JGa_PatternOuter
import JGa_PublicDigest
import JGa_PublicDigestPrefix
import JGa_PublicDigestSuffix
import JGa_Reconstruct
import JGa_Semantic
import JGa_SemanticTail
import JGa_ValueBitsSpecs
import JGa_ValueConservation
import JGa_ValueFinish
import JGa_ValueLanes
import JGa_ValueScale
import JGa_ValueSelectors
import JGa_ValueTail
import JGa_WeightShift
import FJa_PoseidonLowOnRun
import FJa_PoseidonPow5
import JGa_Equality
import JFy_Steps
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
