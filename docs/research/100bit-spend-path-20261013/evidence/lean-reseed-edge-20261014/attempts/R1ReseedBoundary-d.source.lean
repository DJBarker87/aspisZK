import R1ParsedStateTrace
import R1OpeningReseedFrame
import R1DuplexPrefixTable

/-! Recover the actual P3 reseed edge from the table before the next absorb.
The decoder receives only a table and state; oracle-dependent equalities
occur in the correctness theorem, not as decoder inputs. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.ReseedBoundary
open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep
variable {M Cv : Type} {L : Nat}

def findCell (T : Table (Addr L) State) (v : State) : Option (Addr L) :=
  theUnique (cellsWith T v fun _ => True)

theorem findCell_correct (p : Params M Cv L) (H : Addr L → State)
    (tr : List (Addr L × State)) (Qtot : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1) (hQ : firstReads emptyTable tr ≤ Qtot)
    (hcoll : ¬ hitsBad (badColl p Qtot) emptyTable tr)
    (T : Table (Addr L) State)
    (hT : ∀ b v, T b = some v → v = H b ∧ Read tr b)
    (a : Addr L) (hcell : T a = some (H a)) :
    findCell T (H a) = some a := by
  apply theUnique_cellsWith
  intro b
  constructor
  · rintro ⟨h, _⟩
    obtain ⟨hv, hr⟩ := hT b (H a) h
    have har := (hT a (H a) hcell).2
    by_contra hne
    exact noColl_injective p Qtot H tr hcons hQ hcoll b a hr har hne hv.symm
  · rintro rfl
    exact ⟨hcell, True.intro⟩

def recover (T : Table (Addr L) State) (endpoint : State) :
    Option (Addr L × State) :=
  match findCell T endpoint with
  | none => none
  | some r => (TrailingStateFrame.tailState r).map fun s => (r, s)

theorem recover_before_next (p : Params M Cv L) (tag : Byte) (hL : 62 ≤ L)
    (H : Addr L → State) (tr : List (Addr L × State)) (Qtot : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1) (hQ : firstReads emptyTable tr ≤ Qtot)
    (hold : ¬ hitsBad (badColl p Qtot) emptyTable tr)
    (htail : ¬ hitsBad (ParsedStateCollision.bad TrailingStateFrame.tailState Qtot)
      emptyTable tr)
    (a c : Addr L) (ha : Read tr a) (hc : Read tr c)
    (hr : Read tr (OpeningReseedFrame.addr tag hL (H a)))
    (hp : c.toBytes.take 32 = bytes (H (OpeningReseedFrame.addr tag hL (H a)))) :
    let r := OpeningReseedFrame.addr tag hL (H a)
    let T := tableBefore emptyTable tr c
    Before tr a r ∧ Before tr r c ∧ T a = some (H a) ∧
      recover T (H r) = some (r, H a) := by
  dsimp only
  let r := OpeningReseedFrame.addr tag hL (H a)
  let T := tableBefore emptyTable tr c
  have har : Before tr a r :=
    ParsedStateTrace.parsed_after TrailingStateFrame.tailState Qtot H tr hcons hQ
      htail a r ha hr (OpeningReseedFrame.tailState_addr tag hL (H a))
  have hrc : Before tr r c := noColl_prefix_after p Qtot H tr hcons hQ hold r c hr hc hp
  have hac := before_trans tr har hrc
  have hacell : T a = some (H a) := by
    change tableBefore emptyTable tr c a = some (H a)
    rw [tableBefore_eq H tr emptyTable c a hcons, if_pos hac]
  have hrcell : T r = some (H r) := by
    change tableBefore emptyTable tr c r = some (H r)
    rw [tableBefore_eq H tr emptyTable c r hcons, if_pos hrc]
  refine ⟨har, hrc, hacell, ?_⟩
  have hfind := findCell_correct p H tr Qtot hcons hQ hold T
    (DuplexPrefixTable.table_consistent H tr hcons c) r hrcell
  change recover T (H r) = some (r, H a)
  simp only [recover, hfind, r, OpeningReseedFrame.tailState_addr, Option.map_some]

#print axioms findCell_correct
#print axioms recover_before_next
end AspisR1.ReseedBoundary
end
