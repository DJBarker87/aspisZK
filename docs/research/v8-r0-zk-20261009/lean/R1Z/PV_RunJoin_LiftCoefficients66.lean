import R1Z.PV_RunJoin_LiftColumnsValue66
import R1Z.PV_RunJoin_ActualData59
import R1Z.PV_RunJoin_BackendRawCoefficients58
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_LiftCoefficients66
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
open PV_RunJoin_BackendMRows58 (Columns column element)
open PV_RunJoin_LiftArray66 (Row Matrix matrix filled)
open PV_RunJoin_LiftColumnsValue66 (tails vec)
open ProverCommitPrimitive47 ProverCommitNativeOps47
abbrev Q := aspis_core.field.QM31

def coefficients (a : Matrix) (l j : Nat) : Old.Q :=
  normalize (PV_RunJoin_SemanticScalar50.raw
    (((a.val[l]?).map (fun c => c.val[j]?.getD PV_RunJoin_ActualData59.zeroQ)).getD PV_RunJoin_ActualData59.zeroQ))

theorem read (p : Nat → Row) (l j : Nat) (hl : l<29) :
    coefficients (matrix p) l j=normalize (PV_RunJoin_SemanticScalar50.raw
      ((p l).val[j]?.getD PV_RunJoin_ActualData59.zeroQ)) := by
  simp only [coefficients,matrix,ProverCommitArray49.array,List.getElem?_ofFn,
    show l<(29#usize).val from hl,dif_pos,Option.map_some,Option.getD_some]

theorem row_read (columns : Columns)
    (hlen : ∀ l,l<26 → (column columns l).length=1024) (l j : Nat) (hj : j<1024) :
    (PV_RunJoin_LiftRowValue66.row columns hlen l).val[j]?=
      some (PV_RunJoin_LiftCell63.lifted (element columns hlen l j)) := by
  simp only [PV_RunJoin_LiftRowValue66.row,PV_RunJoin_LiftPayload66.payload,
    List.getElem?_ofFn,hj,dif_pos,Nat.zero_add]

attribute [local irreducible] PV_RunJoin_LiftPayload66.payload

/-- Normalize the actual stored lift result, matching the actual backend
constructor coefficients cell by cell, including the helper and both tails. -/
theorem complete (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (columns : Columns)
    (hlen : ∀ l,l<26 → (column columns l).length=1024)
    (h : Row) (hh : h.length=1024) (g d : Array Q 1024#usize) (out : Matrix)
    (success : @host_semantic.lift_columns (types base) (selected base heap box ops) columns h g d=ok out)
    (l j : Nat) (hl : l<29) (hj : j<1024) :
    coefficients out l j=
      PV_RunJoin_BackendRawCoefficients58.coefficients columns hlen d (alloc.vec.Vec.deref h) hh g l j := by
  obtain ⟨p,eq⟩ := PV_RunJoin_LiftColumnsValue66.source base heap box ops columns hlen h g d out success
  rw [eq,read _ l j hl]
  by_cases baseLane : l<26
  · have n26 : l≠26 := by omega
    have n27 : l≠27 := by omega
    have n28 : l≠28 := by omega
    simp only [tails,Function.update_of_ne n28,Function.update_of_ne n27,Function.update_of_ne n26,
      filled,if_pos baseLane,row_read columns hlen l j hj,Option.getD_some,
      PV_RunJoin_BackendRawCoefficients58.coefficients,if_pos baseLane]
    exact PV_RunJoin_LiftCell63.normalized _
  · by_cases lane26 : l=26
    · subst l
      have jh : j<h.val.length := by change j<h.length;omega
      simp only [tails,Function.update_of_ne (show (26:Nat)≠28 from by decide),
        Function.update_of_ne (show (26:Nat)≠27 from by decide),Function.update_self,
        PV_RunJoin_BackendRawCoefficients58.coefficients,if_neg (by omega : ¬(26:Nat)<26),if_true,
        PV_RunJoin_BackendQInput58.element,PV_RunJoin_BackendHRows58.array,Nat.mod_eq_of_lt hj,
        List.getElem?_eq_getElem jh,Option.getD_some]
    · by_cases lane27 : l=27
      · subst l
        have jg : j<g.val.length := by rw [g.property];exact hj
        simp only [tails,Function.update_of_ne (show (27:Nat)≠28 from by decide),Function.update_self,
          PV_RunJoin_BackendRawCoefficients58.coefficients,if_neg (by omega : ¬(27:Nat)<26),
          if_neg (by decide : ¬(27:Nat)=26),if_true,vec,
          PV_RunJoin_BackendQInput58.element,Nat.mod_eq_of_lt hj,List.getElem?_eq_getElem jg,Option.getD_some]
      · have lane28 : l=28 := by omega
        subst l
        have jd : j<d.val.length := by rw [d.property];exact hj
        simp only [tails,Function.update_self,
          PV_RunJoin_BackendRawCoefficients58.coefficients,if_neg (by omega : ¬(28:Nat)<26),
          if_neg (by decide : ¬(28:Nat)=26),if_neg (by decide : ¬(28:Nat)=27),vec,
          PV_RunJoin_BackendQInput58.element,Nat.mod_eq_of_lt hj,List.getElem?_eq_getElem jd,Option.getD_some]

#print axioms coefficients
#print axioms read
#print axioms row_read
#print axioms complete
end R1Z.PV_RunJoin_LiftCoefficients66
