import NNG_FinishRoots094
import NNG_PrefixRoot094
import NNG_Parse137
import NNG_ReturnedPath137
import NNG_FinishReturn137
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_ObservedRoots094
open Aeneas Aeneas.Std Result NMP_prepare NMP_Transport
/-- C1 is tied to the input of the SAME observed semantic call. The second
root remains the actual source output, with no selected replacement value. -/
theorem returned (env : RSL.Env) (s : NNG_Context137.Parent Unit) (out : r1_semantic.Verified Unit)
 (native : NNG_Context137.emitted (NNG_Context137.calls env) s=.ok (.Ok out)) :
 ∃ root0 root1,(toT11 out).roots=Array.make 2#usize [root0,root1] ∧ root0.val=s.bytes.val.take 32 := by
 obtain ⟨p,t,ch,after,parsed,_,_,finish⟩ := NNG_ReturnedPath137.returned env s out native
 obtain ⟨parsedPrefix,source,same⟩ := NNG_Parse137.succeeded s.bytes p parsed
 subst p
 have actual := NNG_FinishReturn137.returned env s.digest s.publicValue
  (fromT13 (LIB_VCarriers.prefixRaw parsedPrefix)) after ch s.observer out finish
 obtain ⟨root,roots⟩ := NNG_FinishRoots094.returned env _ (NNG_Output137.verified out) actual
 have prefixEq : NNG_Transport.toT12
  (NNG_FinishAdapter137.childInput s.digest (toT9 s.publicValue)
   (LIB_VCarriers.prefixRaw parsedPrefix) (toT10 after) (toT3 ch) s.observer).prefixValue=
  LIB_VCarriers.prefixRaw parsedPrefix := by
  change NNG_Transport.toT12 (NNG_Transport.fromT12 (LIB_VCarriers.prefixRaw parsedPrefix))=_
  exact NNG_Transport.fromT12_inverse _
 simp only [fromT13_inverse] at roots
 have moved := roots.trans (congrArg (fun r : Array U8 32#usize=>Array.make 2#usize [r,root])
  (congrArg AspisR1PublicPreparation.r1_wire.Prefix.c1_root prefixEq))
 refine ⟨(LIB_VCarriers.prefixRaw parsedPrefix).c1_root,root,?_,?_⟩
 · simpa only [NNG_Output137.verified,NNG_Transport.fromT11_inverse] using moved
 · exact (congrArg Subtype.val (LIB_VCarriers.prefix_fields parsedPrefix).1).trans
    (NNG_PrefixRoot094.root s.bytes parsedPrefix source)
#print axioms returned
end AspisR1.NNG_ObservedRoots094
