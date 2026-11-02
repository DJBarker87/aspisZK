import R1Z.PV_RunJoin_LiftColumnsValue66
import R1Z.PV_RunJoin_NativePointClaims72
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_LiftRows72
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
open PV_RunJoin_BackendMRows58 (Columns column)
open PV_RunJoin_LiftArray66 (Row Matrix matrix filled)
open PV_RunJoin_LiftColumnsValue66 (tails vec)

theorem row_length (columns : Columns)
    (hlen : ∀ l,l<26 → (column columns l).length=1024) (lane : Nat) :
    (PV_RunJoin_LiftRowValue66.row columns hlen lane).length=1024 := by
  simp only [PV_RunJoin_LiftRowValue66.row,PV_RunJoin_LiftPayload66.payload,List.length_ofFn]

theorem vec_length (a : Array aspis_core.field.QM31 1024#usize) :
    (vec a).length=1024 := a.property

theorem shape (columns : Columns)
    (hlen : ∀ l,l<26 → (column columns l).length=1024)
    (p : Nat → Row) (h : Row) (hs : h.length=1024)
    (g d : Array aspis_core.field.QM31 1024#usize) :
    PV_RunJoin_NativePointClaims72.Rows
      (matrix (tails (filled p (PV_RunJoin_LiftRowValue66.row columns hlen) 26) h g d)) := by
  intro lane v hl hv
  rw [PV_RunJoin_LiftArray66.read _ lane hl] at hv
  cases Result.ok.inj hv
  by_cases h28 : lane.val=28
  · simp only [tails,h28,Function.update_self];exact vec_length d
  · by_cases h27 : lane.val=27
    · simp only [tails,h27,Function.update_of_ne (by decide : (27:Nat)≠28),Function.update_self]
      exact vec_length g
    · by_cases h26 : lane.val=26
      · simp only [tails,h26,Function.update_of_ne (by decide : (26:Nat)≠28),
          Function.update_of_ne (by decide : (26:Nat)≠27),Function.update_self]
        exact hs
      · have lower : lane.val<26 := by omega
        simp only [tails,Function.update_of_ne h28,Function.update_of_ne h27,
          Function.update_of_ne h26,filled,if_pos lower]
        exact row_length columns hlen lane.val

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (columns : Columns)
    (hlen : ∀ l,l<26 → (column columns l).length=1024)
    (h : Row) (hs : h.length=1024) (g d : Array aspis_core.field.QM31 1024#usize)
    (out : Matrix)
    (success : @host_semantic.lift_columns (types base) (selected base heap box ops) columns h g d=ok out) :
    PV_RunJoin_NativePointClaims72.Rows out := by
  obtain ⟨p,hp⟩ := PV_RunJoin_LiftColumnsValue66.source base heap box ops columns hlen h g d out success
  rw [hp]
  exact shape columns hlen p h hs g d

#print axioms row_length
#print axioms vec_length
#print axioms shape
#print axioms complete
end R1Z.PV_RunJoin_LiftRows72
