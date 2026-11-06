import NKQ_CanonicalBridge
import NJM_InvocationRoots
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKQ_AlphaDomain
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NJG_RoundsCode

theorem full (a : NKQ_MaskCuts.Alpha) (h : NJG_CanonicalPrefix.CanonicalBefore a 10) :
 NKQ_MaskCuts.CanonAlpha a := by
 intro value member
 obtain ⟨i,hi,same⟩:=List.mem_iff_getElem.mp member
 have bound : i<10 := by have len:=a.property;change a.val.length=10 at len;omega
 have canonical:=h ⟨i,bound⟩ bound
 rw [←same]
 exact (NKQ_CanonicalBridge.canonical _).mp canonical

/-- At the SAME source constructor/return branch, the CLOSED134 chain
supplies all-alpha canonicality. No child output or success is a root input. -/
theorem source {H : Type} (native : NJM_RoundsCut.Observations) (cut : NJM_RoundsCut.Cut native)
 (token frame : Nat) (D : aspis_core.Digest32 H) (bytes : Slice U8) (t : r1_wire.SemanticTranscript H) :
 match parsed : AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes with
 | .ok (.Ok pre) =>
   match returned : (PreparedHashCode.run (S1SemanticCode.rounds NJM_RoundJoin.R D (PrefixAdapter.fromOld pre) t)).2 with
   | .ok (.Ok after) => NKQ_MaskCuts.CanonAlpha after.2.1
   | _ => True
 | _ => True := by
 split
 · rename_i pre parsed
   obtain ⟨⟨running,whole⟩,_⟩:=NJM_RoundsClosed.source native cut token frame D bytes pre parsed t
   split
   · rename_i after returned
     rw [whole] at returned
     exact full _ (NJM_RoundsClosed.canonical native cut token frame D (PrefixAdapter.fromOld pre)
       (running,Array.repeat 10#usize aspis_core.field.QM31.ZERO,t) after returned)
   all_goals trivial
 · trivial
#print axioms full
#print axioms source
#print source
end AspisR1.NKQ_AlphaDomain
end
