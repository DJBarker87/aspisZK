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
 obtain ⟨prefix,source,same⟩ := NNG_Parse137.succeeded s.bytes p parsed
 subst p
 have actual := NNG_FinishReturn137.returned env s.digest s.publicValue
  (fromT13 (LIB_VCarriers.prefixRaw prefix)) after ch s.observer out finish
 obtain ⟨root,roots⟩ := NNG_FinishRoots094.returned env _ (NNG_Output137.verified out) actual
 have prefixEq : NNG_Transport.toT12
  (NNG_FinishAdapter137.childInput s.digest (toT9 s.publicValue)
   (LIB_VCarriers.prefixRaw prefix) (toT10 after) (toT3 ch) s.observer).prefixValue=
  LIB_VCarriers.prefixRaw prefix := by
  change NNG_Transport.toT12 (NNG_Transport.fromT12 (LIB_VCarriers.prefixRaw prefix))=_
  exact NNG_Transport.fromT12_inverse _
 simp only [fromT13_inverse] at roots
 rw [prefixEq] at roots
 refine ⟨prefix.parsed.c1_root,root,?_,NNG_PrefixRoot094.root s.bytes prefix source⟩
 simpa only [NNG_Output137.verified,NNG_Transport.fromT11_inverse] using roots
#print axioms returned
end AspisR1.NNG_ObservedRoots094
