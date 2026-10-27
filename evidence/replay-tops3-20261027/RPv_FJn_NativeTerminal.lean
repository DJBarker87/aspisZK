import RPv_FJn_TerminalModel
import RPv_FJn_GatherTerminal
import RPv_FJa_PublicCopy
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJn_NativeTerminal
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeValue (Canon decode)
open FIw_ArrayValue (canonical decoded)
open FIz_ConcretePack (embed)
attribute [local irreducible] R0P.SemSource.terminalValue FIw_PublicModel.ofPublic
  FJn_GatherProjection.claims
/-- Complete native terminal, with its actual84-cell gather transported back
to the SAME original three29-cell claim rows. -/
theorem value (pub : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (claims : FIr_GatherCallback.Claims) (alpha : Array field.QM31 10#usize)
    (c : state_only_prefix.r0.Challenges) (out : field.QM31)
    (hc : FIr_GatherCallback.CanonClaims claims) (ha : canonical alpha)
    (hz : canonical c.zc) (hl : Canon c.lambda) (hchi : Canon c.chi)
    (ht : Canon c.theta) (hm : Canon c.mu)
    (bounds : FJa_PublicBounds.Bounds (FJa_PublicCopy.native (FIq_Carriers.fromPublic pub)))
    (run : pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31 pub claims alpha c=ok (.Ok out)) :
    Canon out ∧ embed (decode out)=
      R0P.SemSource.terminalValue
        (SpendDataMap.mapPublic embed (FIw_PublicModel.ofPublic (FJa_PublicCopy.native (FIq_Carriers.fromPublic pub))))
        (embed (decode c.lambda)) (embed (decode c.chi)) (embed (decode c.theta)) (embed (decode c.mu))
        (fun i=>embed (decoded c.zc i)) ConcretePackBasis.basis
        (fun j l=>embed (FJn_GatherProjection.claims claims j l)) (fun i=>embed (decoded alpha i)) := by
  obtain ⟨selected,sem,c1,mask,g,gather,semantic,parts⟩:=FIq_TerminalParts.reached pub claims alpha c out run
  have cc:=FIr_GatherCanonical.gathered claims selected hc gather
  have back : FIq_Carriers.toPublic (FIq_Carriers.fromPublic pub)=pub := by cases pub <;> rfl
  have constructed:=FJa_PublicCopy.on_statement (FIq_Carriers.fromPublic pub)
  rw [back] at constructed
  have same : sem=FJa_PublicCopy.native (FIq_Carriers.fromPublic pub) :=
    Result.ok.inj (semantic.symm.trans constructed)
  subst sem
  have got:=FJn_TerminalModel.value _ selected alpha c.zc c.lambda c.chi c.theta c.mu out c1 mask g
    cc ha hz hl hchi ht hm bounds parts
  refine ⟨got.1,got.2.trans ?_⟩
  unfold FJn_TerminalModel.model
  exact FJn_GatherTerminal.value embed claims selected gather _ _ _ _ _ _ _ _
#print axioms value
end AspisR1.FJn_NativeTerminal
end
