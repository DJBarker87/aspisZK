import NID_ResumeEmissionTypes
import NID_ResumeFields
set_option autoImplicit false
noncomputable section
namespace NIL_Carriers
open Aeneas Aeneas.Std Result
namespace Fresh
abbrev K := NID_ResumeEmission.aspis_core.field.QM31
abbrev E := NID_ResumeEmission.aspis_core.field.wide_exact.WideExact
abbrev R := NID_ResumeEmission.verifier.Reader
abbrev Err := NID_ResumeEmission.verifier.Error
abbrev V := NID_ResumeEmission.transport.Variant
end Fresh
namespace Cohort
abbrev K := AspisR1Stage2.aspis_core.field.QM31
abbrev E := AspisR1Stage2.aspis_core.field.wide_exact.WideExact
abbrev R := AspisR1Stage2.verifier.Reader
abbrev Err := AspisR1Stage2.verifier.Error
abbrev V := AspisR1Stage2.transport.Variant
end Cohort

def k (x : Fresh.K) : Cohort.K := ⟨⟨x.c0.a,x.c0.b⟩,⟨x.c1.a,x.c1.b⟩⟩
def unK (x : Cohort.K) : Fresh.K := ⟨⟨x.c0.a,x.c0.b⟩,⟨x.c1.a,x.c1.b⟩⟩
def e (x : Fresh.E) : Cohort.E := ⟨k x.c0,k x.c1⟩
def unE (x : Cohort.E) : Fresh.E := ⟨unK x.c0,unK x.c1⟩
def reader (x : Fresh.R) : Cohort.R := ⟨x.bytes,x.at⟩
def unReader (x : Cohort.R) : Fresh.R := ⟨x.bytes,x.at⟩
def variant : Fresh.V → Cohort.V
 | .S1 => .S1 | .S2 => .S2 | .D => .D
def unVariant : Cohort.V → Fresh.V
 | .S1 => .S1 | .S2 => .S2 | .D => .D
def error : Fresh.Err → Cohort.Err
 | .Parse => .Parse | .Semantic => .Semantic | .Transcript => .Transcript
 | .Relation => .Relation | .Merkle => .Merkle | .Query => .Query
 | .Checkpoint => .Checkpoint | .Allocation => .Allocation
def unError : Cohort.Err → Fresh.Err
 | .Parse => .Parse | .Semantic => .Semantic | .Transcript => .Transcript
 | .Relation => .Relation | .Merkle => .Merkle | .Query => .Query
 | .Checkpoint => .Checkpoint | .Allocation => .Allocation

def outer {A B : Type} (f : A → B) : Result A → Result B
 | .ok x => .ok (f x) | .fail err => .fail err | .div => .div
def inner {A B : Type} (f : A → B) : core.result.Result A Fresh.Err → core.result.Result B Cohort.Err
 | .Ok x => .Ok (f x) | .Err err => .Err (error err)
def unInner {A B : Type} (f : A → B) : core.result.Result A Cohort.Err → core.result.Result B Fresh.Err
 | .Ok x => .Ok (f x) | .Err err => .Err (unError err)
def array {A B : Type} {N : Usize} (f : A → B) (a : Array A N) : Array B N :=
 ⟨a.val.map f,by simpa using a.property⟩
def vec {A B : Type} (f : A → B) (a : alloc.vec.Vec A) : alloc.vec.Vec B :=
 ⟨a.val.map f,by simpa using a.property⟩

theorem k_roundtrip (x : Fresh.K) : unK (k x)=x := by cases x with | mk a b => cases a;cases b;rfl
theorem k_reverse (x : Cohort.K) : k (unK x)=x := by cases x with | mk a b => cases a;cases b;rfl
theorem e_roundtrip (x : Fresh.E) : unE (e x)=x := by cases x;simp only [e,unE,k_roundtrip]
theorem e_reverse (x : Cohort.E) : e (unE x)=x := by cases x;simp only [e,unE,k_reverse]
theorem reader_roundtrip (x : Fresh.R) : unReader (reader x)=x := by cases x;rfl
theorem reader_reverse (x : Cohort.R) : reader (unReader x)=x := by cases x;rfl
theorem variant_roundtrip (x : Fresh.V) : unVariant (variant x)=x := by cases x <;> rfl
theorem error_roundtrip (x : Fresh.Err) : unError (error x)=x := by cases x <;> rfl
theorem error_reverse (x : Cohort.Err) : error (unError x)=x := by cases x <;> rfl
#print axioms k_roundtrip
#print axioms k_reverse
#print axioms e_roundtrip
#print axioms e_reverse
#print axioms reader_roundtrip
#print axioms reader_reverse
#print axioms variant_roundtrip
#print axioms error_roundtrip
#print axioms error_reverse
end NIL_Carriers
