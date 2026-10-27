import R1Z.PV_CB3_StagedPair
import R1Z.PV_CB3_StagedComposition
import R1Z.PV_CB3_StagedDecode
import R1Z.PV_CB3_StagedMachinePass
import R1Z.PV_CB3_StagedMachineCarry
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB3_StagedKernel
open Aeneas Aeneas.Std Result ProverRwFull
open PV_CB3_StagedIndex

def pipeline (rank0 : Array U32 8#usize) : Array U32 8#usize :=
  let (rank1,d0) := PV_CB3_StagedMachinePass.pass rank0
  let (rank2,d1) := PV_CB3_StagedMachinePass.pass rank1
  let (rank3,d2) := PV_CB3_StagedMachinePass.pass rank2
  let (rank4,d3) := PV_CB3_StagedMachinePass.pass rank3
  let (rank5,d4) := PV_CB3_StagedMachinePass.pass rank4
  let (rank6,d5) := PV_CB3_StagedMachinePass.pass rank5
  let (rank7,d6) := PV_CB3_StagedMachinePass.pass rank6
  let (rank8,d7) := PV_CB3_StagedMachinePass.pass rank7
  let first := PV_CB3_StagedMachineCarry.carry
    (Array.make 8#usize [d0,d1,d2,d3,d4,d5,d6,d7])
    (U32.wrapping_add (limb rank8 ⟨0,by decide⟩) 1#u32)
  if first.2 then (PV_CB3_StagedMachineCarry.carry first.1 1#u32).1 else first.1

/-- Complete Result of the extracted reference, with all source arithmetic
retained in the typed kernel. Native shipped/reference association is still open. -/
theorem source (block : Array U8 32#usize) :
    PV_CB3_StagedSource.staged_reference.gamma block =
      (do let rank0 ← PV_CB3_StagedSource.staged_reference.words block
          PV_CB3_StagedDecode.decode (pipeline rank0)) := by
  obtain ⟨rank0,hr⟩ := PV_CB3_StagedComposition.words_total block
  simp (config := {zetaHave := true}) only [Aeneas.Std.uncurry,letFun,PV_CB3_StagedSource.staged_reference.gamma,hr,bind_tc_ok,pipeline,
    PV_CB3_StagedMachinePass.source,PV_CB3_StagedMachineCarry.source,read0,lift]
  generalize hp1 : PV_CB3_StagedMachinePass.pass rank0 = p1
  rcases p1 with ⟨rank1,d0⟩
  try dsimp (config := {zeta := true, zetaDelta := true, zetaHave := true}) only [Aeneas.Std.uncurry,letFun]
  generalize hp2 : PV_CB3_StagedMachinePass.pass rank1 = p2
  rcases p2 with ⟨rank2,d1⟩
  try dsimp (config := {zeta := true, zetaDelta := true, zetaHave := true}) only [Aeneas.Std.uncurry,letFun]
  generalize hp3 : PV_CB3_StagedMachinePass.pass rank2 = p3
  rcases p3 with ⟨rank3,d2⟩
  try dsimp (config := {zeta := true, zetaDelta := true, zetaHave := true}) only [Aeneas.Std.uncurry,letFun]
  generalize hp4 : PV_CB3_StagedMachinePass.pass rank3 = p4
  rcases p4 with ⟨rank4,d3⟩
  try dsimp (config := {zeta := true, zetaDelta := true, zetaHave := true}) only [Aeneas.Std.uncurry,letFun]
  generalize hp5 : PV_CB3_StagedMachinePass.pass rank4 = p5
  rcases p5 with ⟨rank5,d4⟩
  try dsimp (config := {zeta := true, zetaDelta := true, zetaHave := true}) only [Aeneas.Std.uncurry,letFun]
  generalize hp6 : PV_CB3_StagedMachinePass.pass rank5 = p6
  rcases p6 with ⟨rank6,d5⟩
  try dsimp (config := {zeta := true, zetaDelta := true, zetaHave := true}) only [Aeneas.Std.uncurry,letFun]
  generalize hp7 : PV_CB3_StagedMachinePass.pass rank6 = p7
  rcases p7 with ⟨rank7,d6⟩
  try dsimp (config := {zeta := true, zetaDelta := true, zetaHave := true}) only [Aeneas.Std.uncurry,letFun]
  generalize hp8 : PV_CB3_StagedMachinePass.pass rank7 = p8
  rcases p8 with ⟨rank8,d7⟩
  try dsimp (config := {zeta := true, zetaDelta := true, zetaHave := true}) only [Aeneas.Std.uncurry,letFun]
  generalize hfirst : PV_CB3_StagedMachineCarry.carry
    (Array.make 8#usize [d0,d1,d2,d3,d4,d5,d6,d7])
    (U32.wrapping_add (limb rank8 ⟨0,by decide⟩) 1#u32) = first
  rcases first with ⟨digits,wrapped⟩
  try dsimp (config := {zeta := true, zetaDelta := true, zetaHave := true}) only [Aeneas.Std.uncurry,letFun]
  cases wrapped with
  | false =>
    try dsimp (config := {zeta := true, zetaDelta := true, zetaHave := true}) only [Aeneas.Std.uncurry,letFun]
    simp only [Bool.false_eq_true,ite_false,ite_true,bind_tc_ok]
    simpa only [PV_CB3_StagedDecode.suffix,read0,bind_tc_ok] using PV_CB3_StagedDecode.suffix_eq digits
  | true =>
    generalize hsecond : PV_CB3_StagedMachineCarry.carry digits 1#u32 = second
    rcases second with ⟨digits2,overflow⟩
    try dsimp (config := {zeta := true, zetaDelta := true, zetaHave := true}) only [Aeneas.Std.uncurry,letFun]
    simp only [Bool.false_eq_true,ite_false,ite_true,bind_tc_ok]
    simpa only [PV_CB3_StagedDecode.suffix,read0,bind_tc_ok] using PV_CB3_StagedDecode.suffix_eq digits2
#print axioms source
end R1Z.PV_CB3_StagedKernel
