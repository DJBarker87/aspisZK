import SAQ_WideABI
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAQ_MixedSource
open Aeneas Aeneas.Std Result SAQ_WideABI
/-- The four remainder calls in the emitted canonical_qm31 body. -/
def canonicalQ (q : Q) : Result Q := do
  let a ← q.c0.a % (2147483647#u32)
  let b ← q.c0.b % (2147483647#u32)
  let c ← q.c1.a % (2147483647#u32)
  let d ← q.c1.b % (2147483647#u32)
  ok ⟨⟨a,b⟩,⟨c,d⟩⟩
/-- Exact sequencing of the emitted wide mixed multiplication body. -/
def source (x : W) (q : Q) : Result W := do
  let q ← canonicalQ q
  let a ← AspisR1CurrentWide.field.QM31.mul x.c0 q
  let b ← AspisR1CurrentWide.field.QM31.mul x.c1 q
  ok ⟨a,b⟩

theorem remainder (x : U32) (h : x.val<2147483647) :
    (x % (2147483647#u32) : Result U32)=ok x := by
  obtain ⟨out,run,value⟩ := WP.spec_imp_exists
    (UScalar.rem_spec x (y:=2147483647#u32) (by decide))
  have same : out=x := UScalar.eq_of_val_eq (value.trans (Nat.mod_eq_of_lt h))
  exact run.trans (congrArg Result.ok same)

theorem canonical_same (q : Q) (h : AspisR1CurrentWide.Proof.CanonicalQM q) :
    canonicalQ q=ok q := by
  rcases h with ⟨⟨ha,hb⟩,hc,hd⟩
  simp only [canonicalQ,remainder _ ha,remainder _ hb,remainder _ hc,remainder _ hd,bind_tc_ok]

theorem source_exact (x : W) (q : Q) (z : W)
    (hx : AspisR1CurrentWide.Proof.CanonicalWide x)
    (hq : AspisR1CurrentWide.Proof.CanonicalQM q) (run : source x q=ok z) :
    AspisR1CurrentWide.Proof.CanonicalWide z ∧
    AspisR1CurrentWide.Proof.decodeWide z = AspisR1CurrentWide.Proof.decodeWide x *
      algebraMap OraclePortCheckpointAbiC5.K OraclePortCheckpointAbiC5.E
        (AspisR1CurrentWide.Proof.decodeQM q) := by
  unfold source at run
  rw [canonical_same q hq,bind_tc_ok] at run
  obtain ⟨a,ha,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b,hb,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  have same : (⟨a,b⟩ : W)=z := Result.ok.inj run
  subst z
  have low := AspisR1CurrentWide.Proof.qm_mul_success x.c0 q a hx.1 hq ha
  have high := AspisR1CurrentWide.Proof.qm_mul_success x.c1 q b hx.2 hq hb
  refine ⟨⟨low.1,high.1⟩,?_⟩
  apply QuadraticAlgebra.ext
  · simpa only [AspisR1CurrentWide.Proof.decodeWide,QuadraticAlgebra.re_mul,
      QuadraticAlgebra.algebraMap_re,QuadraticAlgebra.algebraMap_im,mul_zero,zero_mul,add_zero] using low.2
  · simpa only [AspisR1CurrentWide.Proof.decodeWide,QuadraticAlgebra.im_mul,
      QuadraticAlgebra.algebraMap_re,QuadraticAlgebra.algebraMap_im,mul_zero,zero_mul,zero_add,add_zero] using high.2

def mulE (x : E) (q : K) : Result E := do
  let z ← source (toW x) (toQ q)
  ok (fromW z)

theorem mulE_exact (x : E) (q : K) (z : E) (hx : Port4C_QueryArithmetic.CanonE x)
    (hq : Port3_FlushInstall.Canonical q) (run : mulE x q=ok z) :
    CheckpointBytes5Output.ofE z=CheckpointBytes5Output.ofE x *
      LiteralOpeningView.eK (CheckpointBytes5Output.ofK q) ∧ Port4C_QueryArithmetic.CanonE z := by
  obtain ⟨out,ho,he⟩ := Port3_PushFrame.bind_success _ _ _ run
  have same : fromW out=z := Result.ok.inj he
  subst z
  have result := source_exact (toW x) (toQ q) out
    ((w_canonical x).mp hx) ((q_canonical q).mp hq) ho
  constructor
  · simpa only [w_decode,q_decode,toW,fromW,toQ,fromQ,LiteralOpeningView.eK] using result.2
  · exact (w_canonical (fromW out)).mpr result.1

#print axioms remainder
#print axioms canonical_same
#print axioms source_exact
#print axioms mulE_exact
end AspisR1.SAQ_MixedSource
end
