import Aeneas
namespace R1Z.PV_RDB2E_Dispatch
set_option autoImplicit false
inductive Backend where | soft | shani deriving DecidableEq
inductive Cache where | cold | no | yes deriving DecidableEq
structure Features where
  sha : Bool
  sse2 : Bool
  ssse3 : Bool
  sse41 : Bool

def all (f : Features) : Bool := f.sha && f.sse2 && f.ssse3 && f.sse41
def encode : Cache → Nat | .cold => 255 | .no => 0 | .yes => 1
def get (compileAll : Bool) (cpu : Features) (cache : Cache) : Backend × Cache :=
  if compileAll then (.shani,cache) else
  match cache with
  | .yes => (.shani,.yes)
  | .no => (.soft,.no)
  | .cold => if all cpu then (.shani,.yes) else (.soft,.no)

theorem cache_range (c : Cache) : encode c=255 ∨ encode c=0 ∨ encode c=1 := by
  cases c <;> simp [encode]

theorem cold_rule (cpu : Features) :
    (get false cpu .cold).1=if all cpu then .shani else .soft := by
  unfold get; split <;> rfl

theorem compiled_rule (cpu : Features) (cache : Cache) :
    get true cpu cache=(.shani,cache) := rfl

theorem no_rule (cpu : Features) : get false cpu .no=(.soft,.no) := rfl

theorem yes_rule (cpu : Features) : get false cpu .yes=(.shani,.yes) := rfl

theorem cache_initialized (cpu : Features) :
    (get false cpu .cold).2≠.cold := by
  unfold get; split <;> decide

theorem both_reachable :
    (get false ⟨false,false,false,false⟩ .cold).1=.soft ∧
    (get false ⟨true,true,true,true⟩ .cold).1=.shani := ⟨rfl,rfl⟩

#print axioms cache_range
#print axioms cold_rule
#print axioms compiled_rule
#print axioms no_rule
#print axioms yes_rule
#print axioms cache_initialized
#print axioms both_reachable
end R1Z.PV_RDB2E_Dispatch
