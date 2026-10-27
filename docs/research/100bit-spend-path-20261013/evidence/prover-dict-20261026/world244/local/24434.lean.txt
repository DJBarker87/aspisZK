import R1Z.PDict_TapeSource244
import R1Z.PDict_EventWorld244
import R1Z.PDict_Advance244
set_option autoImplicit false
namespace R1Z.PDict_TapeView244
open Aeneas Aeneas.Std Result
abbrev Reply := PDict_TapeSource244.world.Reply
abbrev Tape := PDict_TapeSource244.world.Tape
abbrev World := PDict_EventWorld244.World Unit U8 Reply

def event (reply : Reply) : PDict_EventWorld244.Event U8 Reply :=
  ⟨reply.operation,reply⟩

/-- Exact value map for the owned tag-tape reference. It does not identify a
tag with a whole native syscall request; that additional identity stays open. -/
def view (tape : Tape) : World :=
  ⟨(),0,tape.replies.val.map event,tape.used.val⟩

def next (operation : U8) (world : World) : Option Reply × World :=
  match PDict_EventWorld244.step operation world with
  | none => (none,world)
  | some (reply,after) => (some reply,after)

theorem lookup (tape : Tape) :
    (view tape).files[tape.used.val]? = (tape.replies.val[tape.used.val]?).map event := by
  simp only [view,List.getElem?_map]

theorem capacity (tape : Tape) : (view tape).files.length = 16 := by
  simp only [view,List.length_map,tape.replies.property]
  scalar_tac

theorem advance (tape : Tape) (small : tape.used.val < 16) :
    view {tape with used := Usize.wrapping_add tape.used 1#usize} =
      {view tape with fileUsed := tape.used.val+1} := by
  have h : tape.used.val < 1024 := by omega
  simp only [view,PDict_Advance244.value tape.used h]

theorem source_index (tape : Tape) (small : tape.used.val < 16) :
    ∃ reply : Reply,
      Array.index_usize tape.replies tape.used = .ok reply ∧
      tape.replies.val[tape.used.val]? = some reply := by
  have bound : tape.used.val < tape.replies.length := by scalar_tac
  obtain ⟨reply,run,value⟩ := WP.spec_imp_exists (Array.index_usize_spec tape.replies tape.used bound)
  refine ⟨reply,run,?_⟩
  rw [value]
  exact List.getElem?_eq_getElem bound

#print axioms lookup
#print axioms capacity
#print axioms advance
#print axioms source_index
end R1Z.PDict_TapeView244
