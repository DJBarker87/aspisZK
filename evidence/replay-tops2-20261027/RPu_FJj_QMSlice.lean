import RPu_FJf_QMArray
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJj_QMSlice
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open FIo_FieldBridge (NQ qm)

def canon (s : Slice NQ) : Prop := ∀ x∈s.val,FIo_QMValues.Canon x
def value (s : Slice NQ) (j : Nat) : OraclePortCheckpointAbiC5.K :=
  match s.val[j]? with | some x=>decodeQM (qm x) | none=>0

theorem slot (s : Slice NQ) (i : Usize) (x : NQ)
    (run : Slice.index_usize s i=ok x) : s.val[i.val]?=some x := by
  unfold Slice.index_usize at run
  split at run
  · cases run
  · rename_i v hv
    cases Result.ok.inj run
    exact hv

theorem read (s : Slice NQ) (i : Usize) (x : NQ)
    (run : Slice.index_usize s i=ok x) : value s i.val=decodeQM (qm x) := by
  simp only [value,slot s i x run]

theorem canonical_read (s : Slice NQ) (i : Usize) (x : NQ)
    (hs : canon s) (run : Slice.index_usize s i=ok x) : FIo_QMValues.Canon x :=
  hs x (List.mem_of_getElem? (slot s i x run))

theorem update (s out : Slice NQ) (i : Usize) (x : NQ)
    (run : Slice.update s i x=ok out) : out.val=s.val.set i.val x := by
  unfold Slice.update at run
  split at run
  · cases run
  · cases Result.ok.inj run
    rfl

theorem update_canon (s out : Slice NQ) (i : Usize) (x : NQ)
    (hs : canon s) (hx : FIo_QMValues.Canon x)
    (run : Slice.update s i x=ok out) : canon out := by
  rw [canon,update s out i x run]
  exact FIo_ArrayCanon.list_set FIo_QMValues.Canon _ _ x hs hx

#print axioms slot
#print axioms read
#print axioms canonical_read
#print axioms update
#print axioms update_canon
end AspisR1.FJj_QMSlice
end
