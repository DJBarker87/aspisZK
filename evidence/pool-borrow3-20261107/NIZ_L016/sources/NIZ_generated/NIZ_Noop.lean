import NIK_Invariant
set_option autoImplicit false
namespace NIZ_Noop
open AspisR1.S2Trust

/-- Reviewed transcription of capture-free transition.rs:864 closure. The source
literal returns Ok unit and has no callees or account capabilities; the native
reply/frame controls and (al) stability pair are listed in NIZ_CERTIFICATES.md. -/
def state {F : Type} (s : Heap F) : Heap F := s

def touched (_cell : Nat) : Prop := False

theorem source_scope {F : Type} (s : Heap F) :
    NIK_Invariant.ScopeRun s (state s) := .initial s
#print axioms source_scope

theorem preserves_room {F : Type} (s : Heap F) (a : Nat)
    (room : NIE_BorrowRelease.SharedRoom s a) :
    NIE_BorrowRelease.SharedRoom (state s) a :=
  NIK_Invariant.scope_model_invariant (source_scope s) a room
#print axioms preserves_room

theorem no_held_overlap (guarded : Nat) : ¬ touched guarded := by
  intro impossible
  exact impossible
#print axioms no_held_overlap
end NIZ_Noop
