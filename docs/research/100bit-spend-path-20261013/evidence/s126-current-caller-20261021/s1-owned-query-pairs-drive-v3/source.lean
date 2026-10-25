import S1OwnedQueryPairsRunModelV1
set_option autoImplicit false
namespace AspisS1OwnedQueryPairs.Model
open Aeneas Aeneas.Std Result

def allIndices : List (Fin 8) := List.ofFn (fun k : Fin 8 => k)

theorem allIndices_list : allIndices=[⟨0,by decide⟩,⟨1,by decide⟩,⟨2,by decide⟩,
    ⟨3,by decide⟩,⟨4,by decide⟩,⟨5,by decide⟩,⟨6,by decide⟩,⟨7,by decide⟩] := rfl

def initial : OwnedScan :=
  {accepted:=Array.repeat 22#usize 0#u32,accepted_len:=0#usize,draws:=0#usize}

def drive (ks : List (Fin 8)) (s : OwnedScan) (state : Block) (blocks advances : Blocks) := do
  let (sf,selected) ← walk ks s state blocks advances
  pairs_finish sf selected

theorem drive_nil (s : OwnedScan) (state : Block) (blocks advances : Blocks) :
    drive [] s state blocks advances=pairs_finish s state := rfl

theorem drive_cons (k : Fin 8) (ks : List (Fin 8)) (s : OwnedScan) (state : Block)
    (blocks advances : Blocks) :
    drive (k::ks) s state blocks advances=(do
      let (after,next,stop) ← pairs_step s state (index k) blocks advances
      if stop then pairs_finish after next else drive ks after next blocks advances) := by
  simp only [drive,walk,bind_assoc_eq]
  apply bind_congr
  intro out
  rcases out with ⟨after,next,stop⟩
  cases stop <;> rfl

theorem drive_single (k : Fin 8) (s : OwnedScan) (state : Block) (blocks advances : Blocks) :
    drive [k] s state blocks advances=(do
      let (after,next,_) ← pairs_step s state (index k) blocks advances
      pairs_finish after next) := by
  rw [drive_cons]
  simp only [drive_nil]
  apply bind_congr
  intro out
  rcases out with ⟨after,next,stop⟩
  cases stop <;> rfl

/-- FULL Result equality to the actual emitted eight-call driver. The natural
list recursion is an analysis device; no source limit or caller law is added. -/
theorem reference_eq_drive (blocks advances : Blocks) :
    pairs_reference blocks advances=(do
      let state ← Array.index_usize advances 7#usize
      drive allIndices initial state blocks advances) := by
  unfold pairs_reference
  rw [allIndices_list]
  apply bind_congr
  intro state
  simp only [initial]
  conv => rhs; rw [drive_cons]
  apply bind_congr
  intro out0
  rcases out0 with ⟨s0,state0,stop0⟩
  cases stop0 with
  | true => rfl
  | false =>
    conv => rhs; rw [drive_cons]
    apply bind_congr
    intro out1
    rcases out1 with ⟨s1,state1,stop1⟩
    cases stop1 with
    | true => rfl
    | false =>
      conv => rhs; rw [drive_cons]
      apply bind_congr
      intro out2
      rcases out2 with ⟨s2,state2,stop2⟩
      cases stop2 with
      | true => rfl
      | false =>
        conv => rhs; rw [drive_cons]
        apply bind_congr
        intro out3
        rcases out3 with ⟨s3,state3,stop3⟩
        cases stop3 with
        | true => rfl
        | false =>
          conv => rhs; rw [drive_cons]
          apply bind_congr
          intro out4
          rcases out4 with ⟨s4,state4,stop4⟩
          cases stop4 with
          | true => rfl
          | false =>
            conv => rhs; rw [drive_cons]
            apply bind_congr
            intro out5
            rcases out5 with ⟨s5,state5,stop5⟩
            cases stop5 with
            | true => rfl
            | false =>
              conv => rhs; rw [drive_cons]
              apply bind_congr
              intro out6
              rcases out6 with ⟨s6,state6,stop6⟩
              cases stop6 with
              | true => rfl
              | false =>
                conv => rhs; rw [drive_single]
                rfl

#print axioms drive_cons
#print axioms drive_single
#print axioms reference_eq_drive
end AspisS1OwnedQueryPairs.Model
