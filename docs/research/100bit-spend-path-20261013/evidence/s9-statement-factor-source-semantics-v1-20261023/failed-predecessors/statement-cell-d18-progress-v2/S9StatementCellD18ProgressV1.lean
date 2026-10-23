import S9ConstructorV3StatementCellSemanticsV1
import S9ConstructorV3TauCoordinatesV1
import S9ConstructorV3BilinearCellReadsV1
import S9FactorTableSemanticsV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1S9StatementCellD18ProgressV1
open AspisR1S9ConstructorV3Loop2InnerCanonicalV1
open AspisR1S9ConstructorV3StatementCellCanonicalV1
open AspisR1S9ConstructorV3QMMulSemanticsV1
open AspisR1S9FactorArrayEntryV1 AspisR1S9FactorNestedWriteV1
abbrev E := AspisR1.ExtractedCurrentQM31Exact.QM31Exact

def pointValue (points : StatementPoints) (k i : Nat) : E :=
  match points.val[k]? with
  | none => 0
  | some row => match row.val[i]? with
    | none => 0
    | some q => decode q

def expected (points : StatementPoints) (k : Nat) (d : Usize) (hd : d.val<5) (s : Nat) : E :=
  AspisR1.pairFactor
    (pointValue points k (9-2*(AspisR1.d18Tau ⟨d.val,hd⟩).val))
    (pointValue points k (8-2*(AspisR1.d18Tau ⟨d.val,hd⟩).val)) s

private theorem array_read_lookup {A : Type} {n : Usize} (a : Array A n) (i : Usize) (v : A)
    (h : Array.index_usize a i = .ok v) : a.val[i.val]?=some v := by
  unfold Array.index_usize at h
  cases hr : a[i]? with
  | none => simp [hr] at h
  | some original =>
    rw [hr] at h
    have he : original=v := Result.ok.inj h
    exact he ▸ (by simpa using hr)

theorem point_value_read (points : StatementPoints) (k i : Usize) (row : StatementRow) (q : Q)
    (hr : Array.index_usize points k=.ok row) (hq : Array.index_usize row i=.ok q) :
    pointValue points k.val i.val=decode q := by
  simp only [pointValue,array_read_lookup _ _ _ hr,array_read_lookup _ _ _ hq]

/-- A same accepted source step transports the full stored table meaning to
one D18 pair-factor update, preserving every other decoded table entry. -/
theorem actual_statement_cell_d18_progress
    (points : StatementPoints) (k : Usize) (iter iterNext : R)
    (factors out : Factors) (model : AspisR1S9FactorTableSemanticsV1.Table)
    (hp : StatementPointsCanonical points)
    (hm : AspisR1S9FactorTableSemanticsV1.Meaning factors model)
    (hend : iter.end.val=5)
    (hbody : AspisR1S9ActualWeightsNewBoxNewV3.weights_new_loop0_loop0.body
      points k iter factors=.ok (.cont (iterNext,out))) :
    ∃ (d : Usize) (hd : d.val<5),
      core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=.ok (some d,iterNext) ∧
      AspisR1S9FactorTableSemanticsV1.Meaning out
        (AspisR1S9FactorTableSemanticsV1.write model k.val d.val (expected points k.val d hd)) := by
  obtain ⟨d,tau,i1,ia,i3,ib,point,a,b,q0,q1,q2,q3,old,back,rowOut,
    hnext,htau,hi1,hia,hpoint,ha,hi3,hib,hb,hmut,hrow,hout,
    hc0,hc1,hc2,hc3,hd0,hd1,hd2,hd3⟩ :=
    AspisR1S9ConstructorV3StatementCellSemanticsV1.statement_cell_body_success_semantics
      points k iter iterNext factors out hp hbody
  obtain ⟨hlt,hdEq,hstart,hendNext⟩ := next_some_progress iter iterNext d hnext
  have hd : d.val<5 := by omega
  have hk3 : k.val<3 := by simpa using index_success_bound points k point hpoint
  have hk : k.val<5 := by omega
  have ht := AspisR1S9ConstructorV3TauCoordinatesV1.tau_read_coordinates d tau hd htau
  have hi1e : Usize.wrapping_mul 2#usize tau=i1 := Result.ok.inj hi1
  have hi3e : Usize.wrapping_mul 2#usize tau=i3 := Result.ok.inj hi3
  have hiae : Usize.wrapping_sub 9#usize i1=ia := Result.ok.inj hia
  have hibe : Usize.wrapping_sub 8#usize i3=ib := Result.ok.inj hib
  have iaVal : ia.val=9-2*(AspisR1.d18Tau ⟨d.val,hd⟩).val := by
    rw [←hiae,←hi1e]; exact ht.2.1
  have ibVal : ib.val=8-2*(AspisR1.d18Tau ⟨d.val,hd⟩).val := by
    rw [←hibe,←hi3e]; exact ht.2.2
  have haValue := point_value_read points k ia point a hpoint ha
  have hbValue := point_value_read points k ib point b hpoint hb
  let fresh : Cell := Array.make 4#usize [q0,q1,q2,q3]
  have hc : ∀ (i : Usize) (hi : i.val<4),
      decode (atN fresh i hi)=expected points k.val d hd i.val := by
    intro i hi
    have hr := index_atN fresh i hi
    have hmeaning := AspisR1S9ConstructorV3BilinearCellReadsV1.make4_read_pairFactor
      a b q0 q1 q2 q3 hd0 hd1 hd2 hd3 i (atN fresh i hi) hr
    unfold expected
    rw [←iaVal,←ibVal,haValue,hbValue]
    exact hmeaning
  refine ⟨d,hd,hnext,?_⟩
  rw [hout]
  exact AspisR1S9FactorTableSemanticsV1.accepted_write_meaning
    factors model k d old rowOut back fresh (expected points k.val d hd) hk hd hm hc hmut hrow

#print axioms point_value_read
#print axioms actual_statement_cell_d18_progress
end AspisR1S9StatementCellD18ProgressV1
