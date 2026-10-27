import RPu_FJn_FormulaMap
import RPu_FJn_EqualityArrays
import RPu_FJn_NativeCarrierBridge
import RPu_FIr_RootRefined
import RPu_FIw_CompositionOrigins
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJn_TerminalValueBridge
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeValue (Canon decode)
open FIw_ArrayValue (canonical decoded)
open FIw_CompositionOrigins (SemPub composition)
open FIz_ConcretePack (embed)
attribute [local irreducible] R0P.SemSource.eqValue FJn_FormulaMap.formula
/-- Native terminal tail in Wide, requiring only canonical actual composition
outputs; those canonicalities are supplied by the checked composition producer. -/
theorem value (p : SemPub) (claims : Array field.QM31 84#usize)
    (point zc : Array field.QM31 10#usize) (lambda chi theta mu out : field.QM31)
    (c1 : Array field.QM31 16#usize) (mask : Array field.QM31 10#usize) (g : field.QM31)
    (hc : canonical claims) (hp : canonical point) (hz : canonical zc) (hm : Canon mu)
    (run : FIr_TerminalTrace.parts p claims point lambda chi theta zc mu=ok (.Ok (out,c1,mask,g))) :
    ∃ comp h active,
      composition p claims point lambda chi theta=ok (.Ok (comp,c1,mask,g,h,active)) ∧
      (Canon comp → Canon active → Canon out ∧ embed (decode out)=FJn_FormulaMap.formula
        (R0P.SemSource.eqValue (fun i=>embed (decoded zc i)) (fun i=>embed (decoded point i)))
        (embed (decode comp)) (embed (decode mu)) (embed (decode h)) (embed (decode active))) := by
  obtain ⟨comp,h,active,called,hh,finish⟩:=
    FIr_RootRefined.parts p claims point zc lambda chi theta mu out c1 mask g run hc hz hp hm
  refine ⟨comp,h,active,called,?_⟩
  intro cc ca
  have got:=finish cc ca
  have native : decode out=FIr_TerminalValue.formula
      (R0P.SemSource.eqValue (fun i : Fin 10=>FIv_NativeArray.value zc i.val)
        (fun i : Fin 10=>FIv_NativeArray.value point i.val))
      (decode comp) (decode mu) (decode h) (decode active) := got.2
  have wide:=(congrArg embed native).trans (FJn_FormulaMap.value embed _ _ _ _ _)
  have eqv:=FJn_EqualityArrays.value zc point
  refine ⟨got.1,wide.trans ?_⟩
  exact congrArg (fun e=>FJn_FormulaMap.formula e (embed (decode comp)) (embed (decode mu))
    (embed (decode h)) (embed (decode active))) eqv
#print axioms value
end AspisR1.FJn_TerminalValueBridge
end
