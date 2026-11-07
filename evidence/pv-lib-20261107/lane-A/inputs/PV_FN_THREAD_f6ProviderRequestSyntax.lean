import PV_FN_THREAD_f6OriginalTable
set_option autoImplicit false
namespace PV_FN_THREAD_f6ProviderRequestSyntax
open PV_STX2_Syntax PV_STX2_SliceSyntax

/-- Static projection of one emitted straight instruction. The site and callee
id are retained; none at4963 is separately identified as the exact BoxNew token.
This is syntax analysis, not an interpreter run or a prefix-coverage theorem. -/
def call (n : Node) : Option (Nat × Option Nat) :=
  match n with
  | .leaf (.call site fn _ _ _) => some (site.statement,PV_THR2_OffPath.functionId fn)
  | _ => none

def calls (p : PV_STX2_SliceSyntax.Program) := p.body.filterMap call

/-- Accept only straight instructions that cannot hide another request. Every
call has empty cleanup; no loop, dynamic call, branch, copy or drop is ignored. -/
def straight (n : Node) : Bool :=
  match n with
  | .leaf (.storage _ _ _) => true
  | .leaf (.bind _ _ _) => true
  | .leaf (.aggregateMove _ _ _ _) => true
  | .leaf (.ret _ _) => true
  | .leaf (.call _ _ _ _ []) => true
  | _ => false

theorem constructor_calls :
    calls PV_THR2_F124.live =
      [(4933,some 121),(4945,some 121),(4963,none),
       (4980,some 216),(4993,some 217),(5005,some 218)] ∧
    calls PV_THR2_F216.live = [(9135,some 312),(9147,some 313)] ∧
    calls PV_THR2_F218.live = [(9170,some 315)] ∧
    calls PV_THR2_F315.live = [] := by
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem deref_calls :
    calls PV_THR2_F126.live = [(5028,some 222)] ∧
    calls PV_THR2_F222.live = [(9263,some 320)] := by
  exact ⟨rfl,rfl⟩

theorem constructor_straight :
    PV_THR2_F124.live.body.all straight = true ∧
    PV_THR2_F216.live.body.all straight = true ∧
    PV_THR2_F218.live.body.all straight = true ∧
    PV_THR2_F315.live.body.all straight = true := by
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem deref_straight :
    PV_THR2_F126.live.body.all straight = true ∧
    PV_THR2_F222.live.body.all straight = true := by
  exact ⟨rfl,rfl⟩

#print axioms constructor_calls
#print axioms deref_calls
#print axioms constructor_straight
#print axioms deref_straight
end PV_FN_THREAD_f6ProviderRequestSyntax
