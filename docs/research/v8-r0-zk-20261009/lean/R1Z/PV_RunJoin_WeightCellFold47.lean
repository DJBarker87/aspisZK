import R1Z.PV_RunJoin_WeightCellIndices46
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightCellFold47
open Aeneas Aeneas.Std Result

def finite {A B C : Type} (mul : A → B → Result C) (add : C → C → Result C) :
    Nat → Array A 7#usize → Array B 7#usize → Usize → C → Result C
  | 0,_,_,_,sum => ok sum
  | n+1,kp,raw,kind,sum => do
    let x ← Array.index_usize kp kind
    let q ← Array.index_usize raw kind
    let product ← mul x q
    let next ← add sum product
    finite mul add n kp raw (Usize.wrapping_add kind 1#usize) next

theorem seven {A B C : Type} (mul : A → B → Result C) (add : C → C → Result C)
    (a0 a1 a2 a3 a4 a5 a6 : A) (b0 b1 b2 b3 b4 b5 b6 : B) (sum : C) :
    finite mul add 7 (Array.make 7#usize [a0,a1,a2,a3,a4,a5,a6])
      (Array.make 7#usize [b0,b1,b2,b3,b4,b5,b6]) 0#usize sum =
    [(a0,b0),(a1,b1),(a2,b2),(a3,b3),(a4,b4),(a5,b5),(a6,b6)].foldlM
      (fun acc term => do let p ← mul term.1 term.2; add acc p) sum := by
  simp only [finite,
    PV_RunJoin_WeightCellIndices46.index0,PV_RunJoin_WeightCellIndices46.index1,
    PV_RunJoin_WeightCellIndices46.index2,PV_RunJoin_WeightCellIndices46.index3,
    PV_RunJoin_WeightCellIndices46.index4,PV_RunJoin_WeightCellIndices46.index5,
    PV_RunJoin_WeightCellIndices46.index6,
    PV_RunJoin_WeightCounters46.add0,PV_RunJoin_WeightCounters46.add1,
    PV_RunJoin_WeightCounters46.add2,PV_RunJoin_WeightCounters46.add3,
    PV_RunJoin_WeightCellIndices46.add4,PV_RunJoin_WeightCellIndices46.add5,
    bind_tc_ok,List.foldlM_cons,List.foldlM_nil,bind_assoc,
    PV_RunJoin_WeightResult46.ok_bind]

#print axioms seven

theorem source (n : Nat) (kp : Array PV_RunJoin_WeightWide46.E 7#usize)
    (raw : Array PV_RunJoin_WeightCarrier46.Q 7#usize) (kind : Usize)
    (sum : PV_RunJoin_WeightWide46.E) :
    PV_RunJoin_WeightCell46.finite n kp raw kind sum =
      finite PV_B2_251c1.host_weights.mul_qm31
        PV_B2_251c1.aspis_core.field.wide_exact.WideExact.add n kp raw kind sum := by
  induction n generalizing kind sum with
  | zero => rfl
  | succ n ih =>
    simp only [PV_RunJoin_WeightCell46.finite,finite,ih]
#print axioms source
end R1Z.PV_RunJoin_WeightCellFold47
