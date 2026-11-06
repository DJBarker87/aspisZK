import NKV_ParentTrace
set_option autoImplicit false
noncomputable section
namespace NKV_TraceCases
open Aeneas Aeneas.Std Result AspisR1Stage2
open NKV_ParentTrace NKV_StepErasure

theorem third_error {E : Type} (c0 c1 c2 : Indices → Values → NKV_ParentTrace.Tree E)
 (first second third : List E) (error : verifier.Error)
 (i0 i1 i2 : Indices) (v0 v1 v2 : Values)
 (reply0 : c0 NKV_ParentSource.zeroI NKV_ParentSource.zeroV=(first,ok (.Ok (),i0,v0)))
 (reply1 : c1 i0 v0=(second,ok (.Ok (),i1,v1)))
 (reply2 : c2 i1 v1=(third,ok (.Err error,i2,v2))) :
 three c0 c1 c2=(first++(second++third),ok (.Err error)) := by
 rw [three,reply0]
 simp only [next]
 rw [reply1]
 simp only [next]
 rw [reply2]

theorem all_ok {E : Type} (c0 c1 c2 : Indices → Values → NKV_ParentTrace.Tree E)
 (first second third : List E) (i0 i1 i2 : Indices) (v0 v1 v2 : Values)
 (reply0 : c0 NKV_ParentSource.zeroI NKV_ParentSource.zeroV=(first,ok (.Ok (),i0,v0)))
 (reply1 : c1 i0 v0=(second,ok (.Ok (),i1,v1)))
 (reply2 : c2 i1 v1=(third,ok (.Ok (),i2,v2))) :
 three c0 c1 c2=(first++(second++third),ok (.Ok ())) := by
 rw [three,reply0]
 simp only [next]
 rw [reply1]
 simp only [next]
 rw [reply2]
 simp only [next,List.append_nil]

theorem first_abort {E : Type} (c0 c1 c2 : Indices → Values → NKV_ParentTrace.Tree E)
 (events : List E) (error : Aeneas.Std.Error)
 (reply : c0 NKV_ParentSource.zeroI NKV_ParentSource.zeroV=(events,fail error)) :
 three c0 c1 c2=(events,fail error) := by rw [three,reply];rfl

theorem second_abort {E : Type} (c0 c1 c2 : Indices → Values → NKV_ParentTrace.Tree E)
 (first second : List E) (error : Aeneas.Std.Error) (i0 : Indices) (v0 : Values)
 (reply0 : c0 NKV_ParentSource.zeroI NKV_ParentSource.zeroV=(first,ok (.Ok (),i0,v0)))
 (reply1 : c1 i0 v0=(second,fail error)) :
 three c0 c1 c2=(first++second,fail error) := by
 rw [three,reply0]
 simp only [next]
 rw [reply1]

theorem third_abort {E : Type} (c0 c1 c2 : Indices → Values → NKV_ParentTrace.Tree E)
 (first second third : List E) (error : Aeneas.Std.Error)
 (i0 i1 : Indices) (v0 v1 : Values)
 (reply0 : c0 NKV_ParentSource.zeroI NKV_ParentSource.zeroV=(first,ok (.Ok (),i0,v0)))
 (reply1 : c1 i0 v0=(second,ok (.Ok (),i1,v1)))
 (reply2 : c2 i1 v1=(third,fail error)) :
 three c0 c1 c2=(first++(second++third),fail error) := by
 rw [three,reply0]
 simp only [next]
 rw [reply1]
 simp only [next]
 rw [reply2]

#print third_error
#print all_ok
#print first_abort
#print second_abort
#print third_abort
#print axioms third_error
#print axioms all_ok
#print axioms first_abort
#print axioms second_abort
#print axioms third_abort
end NKV_TraceCases
end
