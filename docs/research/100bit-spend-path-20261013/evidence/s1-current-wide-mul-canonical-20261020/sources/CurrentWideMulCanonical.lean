import ExtractedCurrentQM31Mul
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error
namespace AspisR1CurrentWideMul
abbrev field.M31 := AspisR1Qm31ArithmeticProbe.field.M31
abbrev field.CM31 := AspisR1Qm31ArithmeticProbe.field.CM31
abbrev field.QM31 := AspisR1Qm31ArithmeticProbe.field.QM31
abbrev field.QM31.add := AspisR1Qm31ArithmeticProbe.field.QM31.add
abbrev field.cm.CM31.sub := AspisR1Qm31ArithmeticProbe.field.CM31.sub
abbrev field.QM31.mul := AspisR1Qm31ArithmeticProbe.field.QM31.mul
abbrev field.mul_by_r := AspisR1Qm31ArithmeticProbe.field.mul_by_r
structure field.wide_exact.WideExact where
  c0 : field.QM31
  c1 : field.QM31

/-- [aspis_r1_current_wide_mul::field::{aspis_r1_current_wide_mul::field::QM31}::sub]:
    Source: 'lib.rs', lines 20:1-27:5
    Visibility: public -/
def field.QM31.sub
  (self : field.QM31) (rhs : field.QM31) : Result field.QM31 := do
  let c ← field.cm.CM31.sub self.c0 rhs.c0
  let c1 ← field.cm.CM31.sub self.c1 rhs.c1
  ok { c0 := c, c1 }

/-- [aspis_r1_current_wide_mul::field::wide_exact::mul_u]:
    Source: 'lib.rs', lines 54:0-59:1 -/
def field.wide_exact.mul_u (value : field.QM31) : Result field.QM31 := do
  let c ← field.mul_by_r value.c1
  ok { c0 := c, c1 := value.c0 }

/-- [aspis_r1_current_wide_mul::field::wide_exact::{aspis_r1_current_wide_mul::field::wide_exact::WideExact}::mul]:
    Source: 'lib.rs', lines 38:0-52:5
    Visibility: public -/
def field.wide_exact.WideExact.mul
  (self : field.wide_exact.WideExact) (rhs : field.wide_exact.WideExact) :
  Result field.wide_exact.WideExact
  := do
  let ac ← field.QM31.mul self.c0 rhs.c0
  let bd ← field.QM31.mul self.c1 rhs.c1
  let q ← field.QM31.add self.c0 self.c1
  let q1 ← field.QM31.add rhs.c0 rhs.c1
  let cross ← field.QM31.mul q q1
  let q2 ← field.wide_exact.mul_u bd
  let q3 ← field.QM31.add ac q2
  let q4 ← field.QM31.sub cross ac
  let q5 ← field.QM31.sub q4 bd
  ok { c0 := q3, c1 := q5 }

/-- [aspis_r1_current_wide_mul::wide_mul_entry]:
    Source: 'lib.rs', lines 62:0-62:124
    Visibility: public -/
def wide_mul_entry
  (a : field.wide_exact.WideExact) (b : field.wide_exact.WideExact) :
  Result field.wide_exact.WideExact
  := do
  field.wide_exact.WideExact.mul a b



abbrev CanonicalQM := AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
abbrev CanonicalCM := AspisR1.ExtractedCurrentTowerAdd.CanonicalCM

def CanonicalWide (x : field.wide_exact.WideExact) : Prop :=
  CanonicalQM x.c0 ∧ CanonicalQM x.c1

theorem qm_sub_total (a b : field.QM31) (ha : CanonicalQM a) (hb : CanonicalQM b) :
    ∃ c, field.QM31.sub a b = .ok c ∧ CanonicalQM c := by
  obtain ⟨lo, hlo, clo, _, _⟩ :=
    AspisR1.ExtractedCurrentTowerAdd.current_cm_sub_mod a.c0 b.c0 ha.1 hb.1
  obtain ⟨hi, hhi, chi, _, _⟩ :=
    AspisR1.ExtractedCurrentTowerAdd.current_cm_sub_mod a.c1 b.c1 ha.2 hb.2
  refine ⟨⟨lo,hi⟩, ?_, clo, chi⟩
  simp only [field.QM31.sub, field.cm.CM31.sub,
    hlo, hhi, bind_tc_ok]

theorem by_r_total (a : field.CM31) (ha : CanonicalCM a) :
    ∃ c, field.mul_by_r a = .ok c ∧ CanonicalCM c := by
  obtain ⟨aa, haa, _, caa⟩ :=
    AspisR1.ExtractedCurrentM31AddSub.current_add_mod a.a a.a ha.1 ha.1
  obtain ⟨lo, hlo, _, clo⟩ :=
    AspisR1.ExtractedCurrentM31AddSub.current_sub_mod aa a.b caa ha.2
  obtain ⟨bb, hbb, _, cbb⟩ :=
    AspisR1.ExtractedCurrentM31AddSub.current_add_mod a.b a.b ha.2 ha.2
  obtain ⟨hi, hhi, _, chi⟩ :=
    AspisR1.ExtractedCurrentM31AddSub.current_add_mod a.a bb ha.1 cbb
  refine ⟨⟨lo,hi⟩, ?_, clo, chi⟩
  simp only [field.mul_by_r, AspisR1Qm31ArithmeticProbe.field.mul_by_r,
    AspisR1Qm31ArithmeticProbe.field.M31.double, haa, hlo, hbb, hhi, bind_tc_ok]

theorem mul_u_total (a : field.QM31) (ha : CanonicalQM a) :
    ∃ c, field.wide_exact.mul_u a = .ok c ∧ CanonicalQM c := by
  obtain ⟨r, hr, cr⟩ := by_r_total a.c1 ha.2
  refine ⟨⟨r,a.c0⟩, ?_, cr, ha.1⟩
  simp only [field.wide_exact.mul_u, hr, bind_tc_ok]

theorem wide_mul_total_canonical (a b : field.wide_exact.WideExact)
    (ha : CanonicalWide a) (hb : CanonicalWide b) :
    ∃ c, field.wide_exact.WideExact.mul a b = .ok c ∧ CanonicalWide c := by
  obtain ⟨ac, hac, cac, _⟩ :=
    AspisR1.ExtractedCurrentQM31Mul.current_qm_mul_words a.c0 b.c0 ha.1 hb.1
  obtain ⟨bd, hbd, cbd, _⟩ :=
    AspisR1.ExtractedCurrentQM31Mul.current_qm_mul_words a.c1 b.c1 ha.2 hb.2
  obtain ⟨qa, hqa, cqa, _⟩ :=
    AspisR1.ExtractedCurrentTowerAdd.current_qm_add_mod a.c0 a.c1 ha.1 ha.2
  obtain ⟨qb, hqb, cqb, _⟩ :=
    AspisR1.ExtractedCurrentTowerAdd.current_qm_add_mod b.c0 b.c1 hb.1 hb.2
  obtain ⟨cross, hcross, ccross, _⟩ :=
    AspisR1.ExtractedCurrentQM31Mul.current_qm_mul_words qa qb cqa cqb
  obtain ⟨u, hu, cu⟩ := mul_u_total bd cbd
  obtain ⟨lo, hlo, clo, _⟩ :=
    AspisR1.ExtractedCurrentTowerAdd.current_qm_add_mod ac u cac cu
  obtain ⟨diff, hdiff, cdiff⟩ := qm_sub_total cross ac ccross cac
  obtain ⟨hi, hhi, chi⟩ := qm_sub_total diff bd cdiff cbd
  refine ⟨⟨lo,hi⟩, ?_, clo, chi⟩
  simp only [field.wide_exact.WideExact.mul,
    field.QM31.mul, field.QM31.add,
    hac, hbd, hqa, hqb, hcross, hu, hlo, hdiff, hhi, bind_tc_ok]

#print axioms qm_sub_total
#print axioms by_r_total
#print axioms mul_u_total
#print axioms wide_mul_total_canonical
end AspisR1CurrentWideMul
