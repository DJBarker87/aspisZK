import S9StatementCellD18ProgressV1
import S9ConstructorV3OpeningPointsJoinV1
import S9FactorArrayEntryV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9StatementD18OpeningPointsV1
open AspisR1S9ConstructorV3Loop2InnerCanonicalV1
open AspisR1S9ConstructorV3SuccessorCarryBodyCanonicalV1
open AspisR1S9ConstructorV3VectorMeaningV1
open AspisR1S9ConstructorV3DecodedInputV1
open AspisR1S9ConstructorV3StatementCellCanonicalV1
open AspisR1S9StatementCellD18ProgressV1
open AspisR1S9FactorArrayEntryV1

/-- Total bounded source lookup interpreted using the existing openingPoints.
The two read successes are obtained from actual fixed-size arrays internally. -/
theorem point_value_eq_openingPoints (z : Vector) (points : StatementPoints)
    (hz : VectorCanonical z)
    (hsource : AspisR1S9ActualWeightsNewBoxNewV3.state_only_prefix.r0.statement_points z = .ok points)
    (k : Fin 3) (i : Fin 10) :
    pointValue points k.val i.val = R0P.SemSource.openingPoints
      (fun j : Fin 10 => decodedInput z j.val) k ⟨9-i.val,by omega⟩ := by
  have hk := k.isLt
  have hi := i.isLt
  let ku : Usize := UScalar.ofNatCore .Usize k.val (by scalar_tac)
  let iu : Usize := UScalar.ofNatCore .Usize i.val (by scalar_tac)
  have hku : ku.val=k.val := rfl
  have hiu : iu.val=i.val := rfl
  have hkb : ku.val < (3#usize).val := by change k.val < 3; exact hk
  let row := atN points ku hkb
  have hrow := index_atN points ku hkb
  have hib : iu.val < (10#usize).val := by change i.val < 10; exact hi
  let q := atN row iu hib
  have hq := index_atN row iu hib
  have hlookup := point_value_read points ku iu row q hrow hq
  have hmodel := AspisR1S9ConstructorV3OpeningPointsJoinV1.source_points_success_openingPoints
    z points hz hsource k i ku iu hku hiu row q hrow hq
  rw [hku,hiu] at hlookup
  exact hlookup.trans hmodel

/-- The ACTUAL D18 expected factor uses exactly the two logical model bits
2*tau(d), 2*tau(d)+1. This rewrites the existing expected definition only;
no D18 arithmetic or table invariant is re-proved. -/
theorem expected_eq_openingPoints (z : Vector) (points : StatementPoints)
    (hz : VectorCanonical z)
    (hsource : AspisR1S9ActualWeightsNewBoxNewV3.state_only_prefix.r0.statement_points z = .ok points)
    (k : Fin 3) (d : Usize) (hd : d.val < 5) (s : Nat) :
    expected points k.val d hd s = AspisR1.pairFactor
      (R0P.SemSource.openingPoints (fun j : Fin 10 => decodedInput z j.val) k
        ⟨2*(AspisR1.d18Tau ⟨d.val,hd⟩).val,by have ht := (AspisR1.d18Tau ⟨d.val,hd⟩).isLt; omega⟩)
      (R0P.SemSource.openingPoints (fun j : Fin 10 => decodedInput z j.val) k
        ⟨2*(AspisR1.d18Tau ⟨d.val,hd⟩).val+1,by have ht := (AspisR1.d18Tau ⟨d.val,hd⟩).isLt; omega⟩) s := by
  let tau := AspisR1.d18Tau ⟨d.val,hd⟩
  have ht := tau.isLt
  let a : Fin 10 := ⟨9-2*tau.val,by omega⟩
  let b : Fin 10 := ⟨8-2*tau.val,by omega⟩
  have ha := point_value_eq_openingPoints z points hz hsource k a
  have hb := point_value_eq_openingPoints z points hz hsource k b
  have hia : (⟨9-a.val,by omega⟩ : Fin 10) = ⟨2*tau.val,by omega⟩ := by
    apply Fin.ext
    dsimp only [a]
    omega
  have hib : (⟨9-b.val,by omega⟩ : Fin 10) = ⟨2*tau.val+1,by omega⟩ := by
    apply Fin.ext
    dsimp only [b]
    omega
  unfold expected
  change AspisR1.pairFactor (pointValue points k.val a.val) (pointValue points k.val b.val) s = _
  rw [ha,hb,hia,hib]

#print axioms point_value_eq_openingPoints
#print axioms expected_eq_openingPoints
end AspisR1S9StatementD18OpeningPointsV1
