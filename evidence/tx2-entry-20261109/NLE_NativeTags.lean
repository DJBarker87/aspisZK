import NLE_AuthState
set_option autoImplicit false
namespace NLE_NativeTags
open Aeneas Aeneas.Std VTop_Stages
/-- Finite native oracle tags cover every nominal Rust Error arm. -/
def error (tag : Nat) : verifier.Error := match tag with
 | 0 => .Parse | 1 => .Semantic | 2 => .Transcript | 3 => .Relation
 | 4 => .Merkle | 5 => .Query | 6 => .Checkpoint | _ => .Allocation
def errorTag : verifier.Error → Nat
 | .Parse => 0 | .Semantic => 1 | .Transcript => 2 | .Relation => 3
 | .Merkle => 4 | .Query => 5 | .Checkpoint => 6 | .Allocation => 7
def parse (tag : Nat) : core.result.Result transport.Variant verifier.Error := match tag with
 | 0 => .Ok .S1 | 1 => .Ok .S2 | 2 => .Ok .D | n+3 => .Err (error n)
def parseTag : core.result.Result transport.Variant verifier.Error → Nat
 | .Ok .S1 => 0 | .Ok .S2 => 1 | .Ok .D => 2 | .Err err => errorTag err + 3
def common (tag : Nat) : core.result.Result Unit verifier.Error :=
 if tag = 8 then .Ok () else .Err (error tag)
def commonTag : core.result.Result Unit verifier.Error → Nat
 | .Ok _ => 8 | .Err err => errorTag err
theorem error_roundtrip (err : verifier.Error) : error (errorTag err) = err := by cases err <;> rfl
theorem parse_roundtrip (reply : core.result.Result transport.Variant verifier.Error) :
 parse (parseTag reply) = reply := by
 cases reply with
 | Ok variant => cases variant <;> rfl
 | Err err => cases err <;> rfl
theorem common_roundtrip (reply : core.result.Result Unit verifier.Error) :
 common (commonTag reply) = reply := by
 cases reply with
 | Ok value => cases value; rfl
 | Err err => cases err <;> rfl
theorem parse_domain (reply : core.result.Result transport.Variant verifier.Error) : parseTag reply < 11 := by
 cases reply with
 | Ok variant => cases variant <;> decide
 | Err err => cases err <;> decide
theorem common_domain (reply : core.result.Result Unit verifier.Error) : commonTag reply < 9 := by
 cases reply with
 | Ok value => cases value; decide
 | Err err => cases err <;> decide
#print parse_roundtrip
#print common_roundtrip
#print parse_domain
#print common_domain
#print axioms error_roundtrip
#print axioms parse_roundtrip
#print axioms common_roundtrip
#print axioms parse_domain
#print axioms common_domain
end NLE_NativeTags
