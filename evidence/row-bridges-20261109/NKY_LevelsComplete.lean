import NKY_LevelsRoot
import NKY_LevelsUnique
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKY_LevelsComplete
open Aeneas Aeneas.Std Result
open NJX_AppendDomains (Frontier High)
open NJX_DigestCohort (O dc)
open FIv_NativeValue (Canon)
/-- Exact literal Result for EVERY packet witness of the adopted cohort at
these SAME index/frontier/openings/high. Packet identity cannot hide an output
premise: the chosen witness is eliminated using CLOSED234 determinism. -/
theorem source (index : U64) (f : Frontier) (o : O) (s : High)
 (hf : ∀ d∈f.val,dc d) (ho : FIw_ArrayValue.canonical o)
 (hs : FIw_ArrayValue.canonical s) :
 (∀ packets : NKI_LevelsChildren.Family index f o s,
  NKY_LevelsLiteral.append_levels_packed_selector_tensor NKY_LevelsLiteral.child index f o s=
   ok (NKY_CanonicalLift.cohort index f o s packets)) ∧
 ∃ out : NJX_AppendFold.State,
  NKI_LevelsFrame.run index f o s (List.finRange 20) NKI_LevelsRoot.zero=ok out ∧
  (∀ j,Canon (out j)) ∧
  ∀ packets : NKI_LevelsChildren.Family index f o s,
   NKY_LevelCarrier.pair out=NKY_CanonicalLift.cohort index f o s packets := by
 obtain ⟨p,out,literal,run,value,_trace,hout⟩:=NKY_LevelsRoot.source index f o s hf ho hs
 constructor
 · intro q
   exact literal.trans (congrArg Result.ok (NKY_LevelsUnique.literal_unique index f o s p q))
 · exact ⟨out,run,hout,fun q=>value.trans (NKY_LevelsUnique.literal_unique index f o s p q)⟩
#print source
#print axioms source
end AspisR1.NKY_LevelsComplete
end
