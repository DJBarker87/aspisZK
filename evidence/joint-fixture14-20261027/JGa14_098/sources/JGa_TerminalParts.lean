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
    exact ⟨_,rfl,by assumption⟩
  obtain ⟨result,call,q,same,hq⟩ := WP.spec_imp_exists spec
  exact ⟨q,same ▸ call,hq⟩
#print axioms source
end AspisR1.JGa_TerminalParts
end
