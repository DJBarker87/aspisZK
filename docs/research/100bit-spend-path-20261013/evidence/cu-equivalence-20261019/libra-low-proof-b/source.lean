import AspisR1LibraLow.Funs
import CuSavingsLibraSourceBuilder
import CuSavingsLibraSourcePerm
import CuSavingsLibraConcrete
set_option autoImplicit false
namespace AspisR1.CuSavingsLibraLow
open Aeneas Aeneas.Std Result AspisR1LibraLow
open CuSavingsLibraSourceControl
open CuSavingsWideArithmetic
abbrev ELow := field.wide_exact.WideExact
abbrev Points := Array ELow 4#usize
def zero : ELow := ⟨⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩,⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩⟩
def canonical (x : ELow) : Prop := CanonicalE (toE x)
def decode (x : ELow) : ExactE := decodeE (toE x)
def term (p q : Points) (i : Nat) : ExactE :=
  decode (lookup p zero (CuSavingsLibraSourcePerm.perm (i%4))) *
  decode (lookup q zero (CuSavingsLibraSourcePerm.perm (i/4))) *
    embedding (scalarK 134217728#u32)

theorem quarter_mul : field.M31.mul QUARTER QUARTER=.ok 134217728#u32 := by
  obtain ⟨m,hm,hv,hc⟩ := ExtractedCurrentReducer.current_mul_mod QUARTER QUARTER
  have he : m=134217728#u32 := UScalar.eq_of_val_eq (by
    norm_num [QUARTER,AspisV8R17.RawReducer.P] at hv ⊢
    exact hv)
  simpa only [he] using hm

theorem perm_read (i : Usize) (hi : i.val<4) :
    ∃ out,Array.index_usize PERM i=.ok out ∧ out.val<4 ∧ out.val=CuSavingsLibraSourcePerm.perm i.val := by
  have he : PERM=AspisR1Libra.PERM := by simp only [PERM,AspisR1Libra.PERM]
  rw [he]
  exact CuSavingsLibraSourcePerm.source i hi

theorem callback (p q : Points) (i : Usize) (hi : i.val<16)
    (hp : ∀ j,j<4 → canonical (lookup p zero j))
    (hq : ∀ j,j<4 → canonical (lookup q zero j)) :
    ∃ value,low.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut (p,q) i=.ok (value,(p,q)) ∧
      canonical value ∧ decode value=term p q i.val := by
  obtain ⟨r,hr,hrv⟩ := WP.spec_imp_exists (UScalar.rem_spec i (y:=4#usize) (by scalar_tac))
  obtain ⟨d,hd,hdv⟩ := UScalar.div_spec i (y:=4#usize) (by scalar_tac)
  have hrv' : r.val=i.val%4 := by simpa only [UScalar.ofNatCore_val_eq] using hrv
  have hdv' : d.val=i.val/4 := by simpa only [UScalar.ofNatCore_val_eq] using hdv
  have hr4 : r.val<4 := by rw [hrv'];omega
  have hd4 : d.val<4 := by rw [hdv'];omega
  obtain ⟨ri,hri,hri4,hriv⟩ := perm_read r hr4
  obtain ⟨di,hdi,hdi4,hdiv⟩ := perm_read d hd4
  have hpr := read p zero ri (by scalar_tac)
  have hqr := read q zero di (by scalar_tac)
  obtain ⟨v,hv,hvc,hvv⟩ := CuSavingsWideArithmetic.mul
    (toE (lookup p zero ri.val)) (toE (lookup q zero di.val)) (hp ri.val hri4) (hq di.val hdi4)
  obtain ⟨w,hw,hwc,hwv⟩ := CuSavingsWideArithmetic.scalar v 134217728#u32 (by scalar_tac)
  refine ⟨fromE w,?_,hwc,?_⟩
  · simp only [low.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut,
      hr,hri,hpr,hd,hdi,hqr,field.wide_exact.WideExact.mul,hv,quarter_mul,
      field.wide_exact.WideExact.mul_m31,to_fromE,hw,bind_tc_ok]
  · change decodeE w=term p q i.val
    rw [hwv,hvv]
    simp only [term,decode,hriv,hdiv,hrv',hdv']

#print axioms quarter_mul
#print axioms perm_read
#print axioms callback
end AspisR1.CuSavingsLibraLow
