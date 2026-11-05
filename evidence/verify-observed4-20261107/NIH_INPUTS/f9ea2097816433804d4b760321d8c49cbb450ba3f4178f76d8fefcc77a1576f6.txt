import NIH_RawExtension
import RPv_RawPoseidonExtensionSlice
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.NIH_RawSource

def port : Result FIq_Native.field.QM31 → Result AspisR1SelectedMaskProbe.field.QM31
 | .ok q => ok ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
 | .fail error => .fail error
 | .div => .div

theorem source (limbs : Array U64 4#usize) :
 port (FIq_Native.state_only_poseidon.extension_from_raw_limbs limbs)=
 AspisR1SelectedMaskProbe.state_only_poseidon.extension_from_raw_limbs limbs := by
 have h0:=ExtractedMaskHornerStep.array_index_usize_ok limbs 0#usize (by decide)
 have h1:=ExtractedMaskHornerStep.array_index_usize_ok limbs 1#usize (by decide)
 have h2:=ExtractedMaskHornerStep.array_index_usize_ok limbs 2#usize (by decide)
 have h3:=ExtractedMaskHornerStep.array_index_usize_ok limbs 3#usize (by decide)
 have v0 : (0#usize).val=0 := by decide
 have v1 : (1#usize).val=1 := by decide
 have v2 : (2#usize).val=2 := by decide
 have v3 : (3#usize).val=3 := by decide
 simp only [v0,v1,v2,v3] at h0 h1 h2 h3
 obtain ⟨a,ra,_,_⟩:=NFQ_Reduce.source (limbs.val[0]'(by scalar_tac))
 obtain ⟨b,rb,_,_⟩:=NFQ_Reduce.source (limbs.val[1]'(by scalar_tac))
 obtain ⟨c,rc,_,_⟩:=NFQ_Reduce.source (limbs.val[2]'(by scalar_tac))
 obtain ⟨d,rd,_,_⟩:=NFQ_Reduce.source (limbs.val[3]'(by scalar_tac))
 simp only [FIq_Native.state_only_poseidon.extension_from_raw_limbs,
  AspisR1SelectedMaskProbe.state_only_poseidon.extension_from_raw_limbs,
  h0,h1,h2,h3,NIH_RawReduce.transport,ra,rb,rc,rd,
  FIq_Native.field.CM31.new,AspisR1SelectedMaskProbe.field.CM31.new,bind_tc_ok,port]

theorem canonical (limbs : Array U64 4#usize) (q : FIq_Native.field.QM31)
 (returned : FIq_Native.state_only_poseidon.extension_from_raw_limbs limbs=ok q) :
 q.c0.a.val<2147483647 ∧ q.c0.b.val<2147483647 ∧
 q.c1.a.val<2147483647 ∧ q.c1.b.val<2147483647 := by
 obtain ⟨a,b,c,d,run,_,_,_,_,ca,cb,cc,cd⟩:=NIH_RawExtension.result limbs
 have same:=Result.ok.inj (returned.symm.trans run)
 subst q
 exact ⟨ca,cb,cc,cd⟩

#print axioms source
#print axioms canonical
end AspisR1.NIH_RawSource
