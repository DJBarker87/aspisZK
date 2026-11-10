P='2147483647'
copies=[
 dict(X='SM',N='AspisR1SelectedMaskProbe.field',mul='eq',defs=['double','neg','CM31.add','CM31.sub','CM31.double','CM31.new','CM31.mul_m31','CM31.square','mul_by_r','QM31.add','QM31.mul','QM31.mul_m31','QM31.square']),
 dict(X='SC',N='AspisR1SemanticCallExtraction.aspis_core.field',mul='eq',defs=['double','CM31.add','CM31.sub','mul_by_r','QM31.add','QM31.mul']),
 dict(X='FIq',N='FIq_Native.field',mul='eq',defs=['double','CM31.add','CM31.sub','CM31.double','CM31.new','CM31.mul_m31','CM31.square','mul_by_r','QM31.add','QM31.sub','QM31.mul','QM31.mul_m31','QM31.square']),
 dict(X='R72',N='AspisR72Sampler.field',mul='total',defs=['double','neg','CM31.add','CM31.sub','CM31.neg','CM31.double','CM31.new','CM31.square','mul_by_r','QM31.add','QM31.sub','QM31.square']),
]
out=[];names=[]
def T(name,body):
  names.append(name);out.append(body.strip('\n')+'\n')
for c in copies:
  X,N=c['X'],c['N']
  out.append(f'/-! ### {N} ({X}) -/\nabbrev {X}_WC (c : {N}.CM31) : Prop := c.a.val ≤ {P} ∧ c.b.val ≤ {P}\nabbrev {X}_WQ (q : {N}.QM31) : Prop := {X}_WC q.c0 ∧ {X}_WC q.c1\n')
  if c['mul']=='eq':
    T(f'{X}_M31_mul_lt',f'''theorem {X}_M31_mul_lt (x y : U32) : ∃ z, {N}.M31.mul x y = ok z ∧ z.val ≤ {P} := by
  obtain ⟨z, hz, hv⟩ := refMul_total x y
  exact ⟨z, by rw [{X}_M31_mul_eq]; exact hz, by omega⟩''')
  else:
    T(f'{X}_M31_mul_lt',f'''theorem {X}_M31_mul_lt (x y : U32) : ∃ z, {N}.M31.mul x y = ok z ∧ z.val ≤ {P} := by
  obtain ⟨z, hz, hv⟩ := {X}_M31_mul_total x y
  exact ⟨z, hz, by omega⟩''')
  d=c['defs']
  if 'double' in d: T(f'{X}_M31_double_weak',f'''theorem {X}_M31_double_weak (x : U32) (hx : x.val ≤ {P}) :
    ∃ z, {N}.M31.double x = ok z ∧ z.val ≤ {P} := by
  unfold {N}.M31.double; rw [{X}_M31_add_eq]; exact refAdd_weak x x hx hx''')
  if 'neg' in d: T(f'{X}_M31_neg_weak',f'''theorem {X}_M31_neg_weak (x : U32) (hx : x.val ≤ {P}) :
    ∃ z, {N}.M31.neg x = ok z ∧ z.val ≤ {P} := by
  obtain ⟨z, hz, hv, _⟩ := refNeg_total x hx
  exact ⟨z, by rw [{X}_M31_neg_eq]; exact hz, by omega⟩''')
  for op,ref in [('add','refAdd_weak'),('sub','refSub_weak')]:
    T(f'{X}_CM31_{op}_weak',f'''theorem {X}_CM31_{op}_weak (a b : {N}.CM31) (ha : {X}_WC a) (hb : {X}_WC b) :
    ∃ z, {N}.CM31.{op} a b = ok z ∧ {X}_WC z := by
  obtain ⟨m, hm, vm⟩ := {ref} a.a b.a ha.1 hb.1
  obtain ⟨m1, hm1, vm1⟩ := {ref} a.b b.b ha.2 hb.2
  refine ⟨({{ a := m, b := m1 }} : {N}.CM31), ?_, vm, vm1⟩
  simp only [{N}.CM31.{op}, {X}_M31_{op}_eq, hm, hm1, bind_tc_ok]''')
  if 'CM31.neg' in d: T(f'{X}_CM31_neg_weak',f'''theorem {X}_CM31_neg_weak (a : {N}.CM31) (ha : {X}_WC a) :
    ∃ z, {N}.CM31.neg a = ok z ∧ {X}_WC z := by
  obtain ⟨m, hm, vm⟩ := {X}_M31_neg_weak a.a ha.1
  obtain ⟨m1, hm1, vm1⟩ := {X}_M31_neg_weak a.b ha.2
  exact ⟨({{ a := m, b := m1 }} : {N}.CM31), by simp only [{N}.CM31.neg, hm, hm1, bind_tc_ok], vm, vm1⟩''')
  if 'CM31.double' in d: T(f'{X}_CM31_double_weak',f'''theorem {X}_CM31_double_weak (a : {N}.CM31) (ha : {X}_WC a) :
    ∃ z, {N}.CM31.double a = ok z ∧ {X}_WC z := by
  unfold {N}.CM31.double; exact {X}_CM31_add_weak a a ha ha''')
  if 'CM31.new' in d: T(f'{X}_CM31_new_weak',f'''theorem {X}_CM31_new_weak (a b : U32) (ha : a.val ≤ {P}) (hb : b.val ≤ {P}) :
    ∃ z, {N}.CM31.new a b = ok z ∧ {X}_WC z := ⟨_, rfl, ha, hb⟩''')
  if 'CM31.mul_m31' in d: T(f'{X}_CM31_mul_m31_weak',f'''theorem {X}_CM31_mul_m31_weak (a : {N}.CM31) (r : U32) :
    ∃ z, {N}.CM31.mul_m31 a r = ok z ∧ {X}_WC z := by
  obtain ⟨m, hm, vm⟩ := {X}_M31_mul_lt a.a r
  obtain ⟨m1, hm1, vm1⟩ := {X}_M31_mul_lt a.b r
  exact ⟨({{ a := m, b := m1 }} : {N}.CM31), by simp only [{N}.CM31.mul_m31, hm, hm1, bind_tc_ok], vm, vm1⟩''')
  if 'CM31.square' in d:
    cross='r23_totalw i4 i9' if X=='R72' else 'cross_okw i4 i9'
    T(f'{X}_CM31_square_weak',f'''theorem {X}_CM31_square_weak (a : {N}.CM31) (ha : {X}_WC a) :
    ∃ z, {N}.CM31.square a = ok z ∧ {X}_WC z := by
  have hPv : ({N}.P).val = {P} := by unfold {N}.P; rfl
  have h1 := ha.1
  have h2 := ha.2
  obtain ⟨i4, h4, v4⟩ := add_ok (core.convert.num.FromU64U32.from a.a) (core.convert.num.FromU64U32.from a.b)
    (by rw [from_val, from_val, max64]; omega)
  obtain ⟨i7, h7, v7⟩ := add_ok (core.convert.num.FromU64U32.from a.a) (core.convert.num.FromU64U32.from {N}.P)
    (by rw [from_val, from_val, hPv, max64]; omega)
  obtain ⟨i9, h9, v9⟩ := sub_ok i7 (core.convert.num.FromU64U32.from a.b)
    (by rw [v7, from_val, from_val, from_val, hPv]; omega)
  obtain ⟨i10, h10, _⟩ := {cross} (by rw [v4, from_val, from_val]; omega)
    (by rw [v9, v7, from_val, from_val, from_val, hPv]; omega)
  obtain ⟨m, hm, vm⟩ := refReduce_total i10
  obtain ⟨m1, hm1, vm1⟩ := {X}_M31_mul_lt a.a a.b
  obtain ⟨m2, hm2, vm2⟩ := {X}_M31_double_weak m1 vm1
  refine ⟨{{ a := m, b := m2 }}, ?_, by omega, vm2⟩
  simp only [{N}.CM31.square, {X}_reduce_wrapper, lift, bind_tc_ok, h4, h7, h9, h10, hm, hm1, hm2]''')
  if 'mul_by_r' in d: T(f'{X}_mul_by_r_weak',f'''theorem {X}_mul_by_r_weak (x : {N}.CM31) (hx : {X}_WC x) :
    ∃ z, {N}.mul_by_r x = ok z ∧ {X}_WC z := by
  obtain ⟨m, hm, vm⟩ := {X}_M31_double_weak x.a hx.1
  obtain ⟨m1, hm1, vm1⟩ := refSub_weak m x.b vm hx.2
  obtain ⟨m2, hm2, vm2⟩ := {X}_M31_double_weak x.b hx.2
  obtain ⟨m3, hm3, vm3⟩ := refAdd_weak x.a m2 hx.1 vm2
  refine ⟨({{ a := m1, b := m3 }} : {N}.CM31), ?_, vm1, vm3⟩
  simp only [{N}.mul_by_r, {X}_M31_sub_eq, {X}_M31_add_eq, hm, hm1, hm2, hm3, bind_tc_ok]''')
  for op in ['add','sub']:
    if f'QM31.{op}' in d: T(f'{X}_QM31_{op}_weak',f'''theorem {X}_QM31_{op}_weak (a b : {N}.QM31) (ha : {X}_WQ a) (hb : {X}_WQ b) :
    ∃ z, {N}.QM31.{op} a b = ok z ∧ {X}_WQ z := by
  obtain ⟨c, hc, vc⟩ := {X}_CM31_{op}_weak a.c0 b.c0 ha.1 hb.1
  obtain ⟨c1, hc1, vc1⟩ := {X}_CM31_{op}_weak a.c1 b.c1 ha.2 hb.2
  refine ⟨({{ c0 := c, c1 := c1 }} : {N}.QM31), ?_, vc, vc1⟩
  simp only [{N}.QM31.{op}, hc, hc1, bind_tc_ok]''')
  if 'QM31.mul' in d: T(f'{X}_QM31_mul_weak',f'''theorem {X}_QM31_mul_weak (a b : {N}.QM31) (ha : {X}_WQ a) (hb : {X}_WQ b) :
    ∃ z, {N}.QM31.mul a b = ok z ∧ {X}_WQ z := by
  obtain ⟨m0, h0, v0a, v0b⟩ := {X}_CM31_mul_weak a.c0 b.c0 ha.1.1 ha.1.2 hb.1.1 hb.1.2
  obtain ⟨m1, h1, v1a, v1b⟩ := {X}_CM31_mul_weak a.c1 b.c1 ha.2.1 ha.2.2 hb.2.1 hb.2.2
  obtain ⟨c, hc, vc⟩ := {X}_CM31_add_weak a.c0 a.c1 ha.1 ha.2
  obtain ⟨c1, hc1, vc1⟩ := {X}_CM31_add_weak b.c0 b.c1 hb.1 hb.2
  obtain ⟨m2, h2, v2a, v2b⟩ := {X}_CM31_mul_weak c c1 vc.1 vc.2 vc1.1 vc1.2
  obtain ⟨c2, hc2, vc2⟩ := {X}_mul_by_r_weak m1 ⟨v1a, v1b⟩
  obtain ⟨c3, hc3, vc3⟩ := {X}_CM31_add_weak m0 c2 ⟨v0a, v0b⟩ vc2
  obtain ⟨c4, hc4, vc4⟩ := {X}_CM31_sub_weak m2 m0 ⟨v2a, v2b⟩ ⟨v0a, v0b⟩
  obtain ⟨c5, hc5, vc5⟩ := {X}_CM31_sub_weak c4 m1 vc4 ⟨v1a, v1b⟩
  refine ⟨({{ c0 := c3, c1 := c5 }} : {N}.QM31), ?_, vc3, vc5⟩
  simp only [{N}.QM31.mul, h0, h1, hc, hc1, h2, hc2, hc3, hc4, hc5, bind_tc_ok]''')
  if 'QM31.mul_m31' in d: T(f'{X}_QM31_mul_m31_weak',f'''theorem {X}_QM31_mul_m31_weak (q : {N}.QM31) (r : U32) :
    ∃ z, {N}.QM31.mul_m31 q r = ok z ∧ {X}_WQ z := by
  obtain ⟨c, hc, vc⟩ := {X}_CM31_mul_m31_weak q.c0 r
  obtain ⟨c1, hc1, vc1⟩ := {X}_CM31_mul_m31_weak q.c1 r
  exact ⟨({{ c0 := c, c1 := c1 }} : {N}.QM31), by simp only [{N}.QM31.mul_m31, hc, hc1, bind_tc_ok], vc, vc1⟩''')
  if 'QM31.square' in d: T(f'{X}_QM31_square_weak',f'''theorem {X}_QM31_square_weak (q : {N}.QM31) (hq : {X}_WQ q) :
    ∃ z, {N}.QM31.square q = ok z ∧ {X}_WQ z := by
  obtain ⟨s0, hs0, vs0⟩ := {X}_CM31_square_weak q.c0 hq.1
  obtain ⟨s1, hs1, vs1⟩ := {X}_CM31_square_weak q.c1 hq.2
  obtain ⟨c, hc, vc⟩ := {X}_mul_by_r_weak s1 vs1
  obtain ⟨c1, hc1, vc1⟩ := {X}_CM31_add_weak s0 c vs0 vc
  obtain ⟨c2, hc2, v2a, v2b⟩ := {X}_CM31_mul_weak q.c0 q.c1 hq.1.1 hq.1.2 hq.2.1 hq.2.2
  obtain ⟨c3, hc3, vc3⟩ := {X}_CM31_double_weak c2 ⟨v2a, v2b⟩
  refine ⟨({{ c0 := c1, c1 := c3 }} : {N}.QM31), ?_, vc1, vc3⟩
  simp only [{N}.QM31.square, hs0, hs1, hc, hc1, hc2, hc3, bind_tc_ok]''')
hdr='''import NPH_R22Producers
import RPu_FIq_Native02

/-! NPH_ (R22, separate limb invariant, step 2): tower lemmas for the SelectedMaskProbe (SM),
SemanticCallExtraction (SC), FIq_Native (FIq) and AspisR72Sampler (R72) copies, in the pattern
of NPH_R22Producers (CW/QA). W is limbs ≤ P. Each reached tower definition of these copies
maps W inputs to an ok W output (mul_m31 for any M31 operand; CM31.square with the weak
Karatsuba bound (2P)^2 < 2^64, through r23_product_u32_bounded for R72). Not covered: the R72
QM31.mul (its first step r24_canonical_mul is OPEN: NO_FROZEN_COUNTERPART) and the FIq
prepared-multiplier family. Standard axioms; no merged module is changed. -/
set_option autoImplicit false
namespace AspisR1.NPH_R22Towers
open Aeneas Aeneas.Std Result AspisR1.NPH_R22FieldRef AspisR1.NPH_R22FieldCopies AspisR1.NPH_R22CM31 AspisR1.NPH_R22Weak

'''
txt=hdr+'\n'.join(out)+'\n'+'\n'.join('#print axioms '+n for n in names)+'\nend AspisR1.NPH_R22Towers\n'
open('NPH_R22Towers.lean','w').write(txt);print(len(names))
