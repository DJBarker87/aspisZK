import R1DuplexPrefixTable

/-! Transfer table-before cells to a later transcript endpoint. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.TableBeforeOrder

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep

variable {M Cv : Type} {L : Nat}

theorem before_of_cell (H : Addr L → State) (tr : List (Addr L × State))
    (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (d a : Addr L) (v : State)
    (hcell : tableBefore emptyTable tr d a = some v) :
    Before tr a d := by
  rw [tableBefore_eq H tr emptyTable d a hcons] at hcell
  split at hcell
  · rename_i hbefore
    exact ⟨hbefore.1, hbefore.2⟩
  · simp [emptyTable] at hcell

theorem transfer (H : Addr L → State) (tr : List (Addr L × State))
    (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (d c : Addr L) (hdc : Before tr d c)
    (a : Addr L) (v : State)
    (hcell : tableBefore emptyTable tr d a = some v) :
    tableBefore emptyTable tr c a = some v := by
  have had : Before tr a d := before_of_cell H tr hcons d a v hcell
  have hval : v = H a :=
    (DuplexPrefixTable.table_consistent H tr hcons d a v hcell).1
  have hac : Before tr a c := before_trans tr had hdc
  rw [tableBefore_eq H tr emptyTable c a hcons, if_pos hac]
  exact congrArg some hval.symm

#print axioms before_of_cell
#print axioms transfer
end AspisR1.TableBeforeOrder
end
