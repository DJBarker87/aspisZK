import PCA_Transcription
set_option autoImplicit false
namespace PCA
namespace Borrow
open Transcription

def Invariant (s : PCA_State) : Prop := NLF_ParentModel.Invariant s.loans

theorem acquire_preserves (site account : Nat) : Preserves Invariant (Plan.acquire site account) := by
  intro k s _ h
  have hx := NLF_ParentModel.acquire_preserves s.loans account .exclusive h
  simp only [Plan.acquire]
  cases hr : (NLF_ParentModel.acquire s.loans account .exclusive).2 <;> exact hx

theorem read_preserves (g : NLF_RefCell.Guard) : Preserves Invariant (Plan.readGuard g) := by
  intro k s _ h
  have hd := NLF_ParentModel.deref_invariant s.loans g h
  cases hr : (NLF_ParentModel.deref s.loans g).2 <;>
    simpa only [Plan.readGuard, hr, Invariant] using hd

theorem copy_preserves (site : Nat) (g : NLF_RefCell.Guard) (bytes : Bytes) :
    Preserves Invariant (Plan.copy site g bytes) := by
  intro k s _ h
  have hd := NLF_ParentModel.deref_invariant s.loans g h
  cases hr : (NLF_ParentModel.deref s.loans g).2 with
  | error e => simpa only [Plan.copy, hr, Invariant] using hd
  | ok payload =>
    simp only [Plan.copy, hr]
    split
    · exact NLF_StateLaws.write_invariant (NLF_ParentModel.deref s.loans g).1 g
        {payload with bytes := bytes} hd
    · exact hd

theorem cleanup_preserves (guards : List NLF_RefCell.Guard) (s : PCA_State) (h : Invariant s) :
    Invariant (cleanup guards s).1 := by
  induction guards generalizing s with
  | nil => exact h
  | cons g gs ih =>
    exact ih {s with loans := (NLF_ParentModel.release s.loans g).1, liveGuards := gs}
      (NLF_ParentModel.release_preserves s.loans g h)

theorem finish_preserves (r : Execution Unit) (h : Invariant r.state) :
    Invariant (finish r).state := by
  cases hr : r.reply with
  | abort reason => simpa only [finish, hr, Invariant] using h
  | ok x => simpa only [finish, hr, Invariant] using cleanup_preserves r.state.liveGuards r.state h
  | error code => simpa only [finish, hr, Invariant] using cleanup_preserves r.state.liveGuards r.state h

#print axioms acquire_preserves
#print axioms read_preserves
#print axioms copy_preserves
#print axioms cleanup_preserves
#print axioms finish_preserves
end Borrow
end PCA
