import json,pathlib
q=[]
def add(body,names,module='PV_L2B_Rejection',ns=None,initial=None):
 q.append(dict(body=body,theorems=names.split(),module=module,namespace=ns or module,**({'initial':initial} if initial else {})))
add('theorem empty {A : Type} (n : Nat) : scan (n+1) ([] : List (Option A)) = (0, none) := rfl','empty')
add('theorem accepted {A : Type} (n : Nat) (a : A) (xs : List (Option A)) : scan (n+1) (some a :: xs) = (1, some a) := rfl','accepted')
add('theorem rejected {A : Type} (n : Nat) (xs : List (Option A)) : scan (n+1) (none :: xs) = ((scan n xs).1+1, (scan n xs).2) := rfl','rejected')
add('''theorem consumed_le_cap {A : Type} (n : Nat) (xs : List (Option A)) : (scan n xs).1 ≤ n := by
  induction n generalizing xs with
  | zero => simp [scan]
  | succ n ih =>
    cases xs with
    | nil => simp [scan]
    | cons x xs => cases x <;> simp [scan]; exact ih xs''','consumed_le_cap')
add('''theorem consumed_le_length {A : Type} (n : Nat) (xs : List (Option A)) : (scan n xs).1 ≤ xs.length := by
  induction n generalizing xs with
  | zero => simp [scan]
  | succ n ih =>
    cases xs with
    | nil => simp [scan]
    | cons x xs => cases x <;> simp [scan]; exact ih xs''','consumed_le_length')
add('''theorem scan_map {A B : Type} (f : A → B) (n : Nat) (xs : List (Option A)) :
    scan n (xs.map (Option.map f)) = ((scan n xs).1, (scan n xs).2.map f) := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih =>
    cases xs with
    | nil => rfl
    | cons x xs => cases x <;> simp [scan, ih]''','scan_map')
add('''theorem count_map {A B : Type} (f : A → B) (n : Nat) (xs : List (Option A)) :
    (scan n (xs.map (Option.map f))).1 = (scan n xs).1 := by rw [scan_map]''','count_map')
add('''theorem status_map {A B : Type} (f : A → B) (n : Nat) (xs : List (Option A)) :
    (scan n (xs.map (Option.map f))).2.isSome = (scan n xs).2.isSome := by
  rw [scan_map]; cases (scan n xs).2 <;> rfl''','status_map')
add('''def trace {A : Type} (n : Nat) (xs : List (Option A)) : Nat × Bool :=
  ((scan n xs).1, (scan n xs).2.isSome)
theorem trace_relabel {A B : Type} (f : A → B) (n : Nat) (xs : List (Option A)) :
    trace n (xs.map (Option.map f)) = trace n xs := by
  simp only [trace, count_map, status_map]''','trace_relabel')
add('''def flags {A : Type} (xs : List (Option A)) : List (Option Unit) := xs.map (Option.map (fun _ => ()))
theorem coins_only {A : Type} (n : Nat) (xs : List (Option A)) :
    trace n xs = trace n (flags xs) := (trace_relabel (fun _ => ()) n xs).symm''','coins_only')
add('''theorem same_flags {A B : Type} (n : Nat) (xs : List (Option A)) (ys : List (Option B))
    (h : flags xs = flags ys) : trace n xs = trace n ys := by
  rw [coins_only n xs, coins_only n ys, h]''','same_flags')
add('''theorem rejected_prefix {A : Type} (r n : Nat) (xs : List (Option A)) :
    scan (r+n) (List.replicate r none ++ xs) =
      (r + (scan n xs).1, (scan n xs).2) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Nat.succ_add, List.replicate_succ, List.cons_append, rejected, ih]
    simp only [Nat.succ_add, Nat.add_succ]''','rejected_prefix')
add('''theorem first_accept {A : Type} (r n : Nat) (a : A) (xs : List (Option A)) :
    scan (r+n+1) (List.replicate r none ++ some a :: xs) = (r+1, some a) := by
  rw [show r+n+1=r+(n+1) by omega, rejected_prefix, accepted]''','first_accept')
add('''theorem exhausted {A : Type} (n : Nat) :
    scan n (List.replicate n (none : Option A)) = (n, none) := by
  have h := rejected_prefix (A := A) n 0 []
  simpa [scan] using h''','exhausted')
add('''theorem accept_in_range (p x : Nat) (h : x < p) :
    (if x < p then some x else none) = some x := if_pos h''','accept_in_range')
add('''theorem reject_at_boundary (p : Nat) :
    (if p < p then some p else none : Option Nat) = none := by simp''','reject_at_boundary')
pathlib.Path('evidence/pv-l2b-20261027/proof-queue.json').write_text(json.dumps(q,indent=2)+'\n')
m='PV_L2B_SamplerLaw'
initial='''import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
set_option autoImplicit false
namespace PV_L2B_SamplerLaw
-- IID path weights, not an axiom identifying SHA outputs with IID words.
def geom (q : ℚ) (r : Nat) : ℚ := q^r * (1-q)
def success (q : ℚ) : Nat → ℚ
  | 0 => 0
  | n+1 => (1-q)+q*success q n
def valueMass (q u : ℚ) : Nat → ℚ
  | 0 => 0
  | n+1 => u+q*valueMass q u n
def prefixMass (q u : ℚ) (r : Nat) : ℚ := q^r*u
end PV_L2B_SamplerLaw
'''
def law(body,names):add(body,names,m,initial=initial if not any(i['module']==m for i in q) else None)
law('theorem geometric_zero (q : ℚ) : geom q 0 = 1-q := by simp [geom]','geometric_zero')
law('theorem geometric_step (q : ℚ) (r : Nat) : geom q (r+1) = q*geom q r := by simp [geom,pow_succ]; ring','geometric_step')
law('theorem success_zero (q : ℚ) : success q 0 = 0 := rfl','success_zero')
law('theorem success_closed (q : ℚ) (n : Nat) : success q n = 1-q^n := by\n  induction n with\n  | zero => simp [success]\n  | succ n ih => rw [success, ih, pow_succ]; ring','success_closed')
law('theorem total_capped (q : ℚ) (n : Nat) : success q n + q^n = 1 := by rw [success_closed]; ring','total_capped')
law('theorem value_factor (q u : ℚ) (n : Nat) (p : ℚ) (h : u*p=1-q) : valueMass q u n * p = success q n := by\n  induction n with\n  | zero => simp [valueMass,success]\n  | succ n ih => simp only [valueMass,success]; calc\n      (u+q*valueMass q u n)*p = u*p+q*(valueMass q u n*p) := by ring\n      _ = (1-q)+q*success q n := by rw [h,ih]','value_factor')
law('theorem uniform_on_success (q u p : ℚ) (n : Nat) (hp : p ≠ 0) (h : u*p=1-q) : valueMass q u n = success q n / p := by\n  apply (eq_div_iff hp).2; exact value_factor q u n p h','uniform_on_success')
law('theorem prefix_independent (q u p : ℚ) (r : Nat) (h : u*p=1-q) : prefixMass q u r * p = geom q r := by\n  unfold prefixMass geom; calc q^r*u*p = q^r*(u*p) := by ring\n  _ = q^r*(1-q) := by rw [h]','prefix_independent')
law('theorem prefix_uniform (q u p : ℚ) (r : Nat) (hp : p ≠ 0) (h : u*p=1-q) : prefixMass q u r = geom q r / p := by\n  apply (eq_div_iff hp).2; exact prefix_independent q u p r h','prefix_uniform')
law('theorem scalar_normalization (p : ℚ) (hp : p+1 ≠ 0) : (1/(p+1))*p = 1-1/(p+1) := by field_simp; ring','scalar_normalization')
law('theorem scalar_trace_law (p : ℚ) (hp : p+1 ≠ 0) (r : Nat) : prefixMass (1/(p+1)) (1/(p+1)) r*p = geom (1/(p+1)) r :=\n  prefix_independent _ _ _ _ (scalar_normalization p hp)','scalar_trace_law')
law('theorem scalar_uniform (p : ℚ) (hp : p ≠ 0) (hp1 : p+1 ≠ 0) (n : Nat) : valueMass (1/(p+1)) (1/(p+1)) n = (1-(1/(p+1))^n)/p := by\n  rw [uniform_on_success _ _ _ _ hp (scalar_normalization p hp1), success_closed]','scalar_uniform')
law('theorem scalar_prefix_product (p : ℚ) (hp : p ≠ 0) (hp1 : p+1 ≠ 0) (r : Nat) : prefixMass (1/(p+1)) (1/(p+1)) r = geom (1/(p+1)) r * (1/p) := by\n  rw [prefix_uniform _ _ _ _ hp (scalar_normalization p hp1)]; ring','scalar_prefix_product')
law('theorem entropy_reject_partition (z : ℚ) : z + (1-z)*z = 1-(1-z)^2 := by ring','entropy_reject_partition')
law('theorem entropy_accept_partition (z : ℚ) : z+(1-z)*z+(1-z)^2=1 := by ring','entropy_accept_partition')
law('theorem entropy_pair_normalization (b : ℚ) (hb : b ≠ 0) : (1/b^2)*(b-1)^2 = 1-(1-(1-1/b)^2) := by field_simp; ring','entropy_pair_normalization')
law('theorem entropy_uniform_pair (b : ℚ) (hb : b ≠ 0) (hn : (b-1)^2 ≠ 0) (n : Nat) :\n  valueMass (1-(1-1/b)^2) (1/b^2) n = success (1-(1-1/b)^2) n / (b-1)^2 :=\n  uniform_on_success _ _ _ _ hn (entropy_pair_normalization b hb)','entropy_uniform_pair')
law('theorem entropy_prefix_pair (b : ℚ) (hb : b ≠ 0) (hn : (b-1)^2 ≠ 0) (r : Nat) :\n  prefixMass (1-(1-1/b)^2) (1/b^2) r = geom (1-(1-1/b)^2) r / (b-1)^2 :=\n  prefix_uniform _ _ _ _ hn (entropy_pair_normalization b hb)','entropy_prefix_pair')
law('theorem geometric_nonnegative (q : ℚ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (r : Nat) : 0 ≤ geom q r :=\n  mul_nonneg (pow_nonneg hq _) (sub_nonneg.mpr hq1)','geometric_nonnegative')
law('theorem exhaustion_nonnegative (q : ℚ) (hq : 0 ≤ q) (n : Nat) : 0 ≤ q^n := pow_nonneg hq n','exhaustion_nonnegative')
law('theorem source_scalar_reject_probability : (1 : ℚ)/((2147483647:ℚ)+1) = 1/(2:ℚ)^31 := by norm_num','source_scalar_reject_probability')
law('theorem source_scalar_exhaustion_probability : ((1:ℚ)/(2:ℚ)^31)^16 = 1/(2:ℚ)^496 := by\n  rw [div_pow, one_pow, ← pow_mul]','source_scalar_exhaustion_probability')
pathlib.Path('evidence/pv-l2b-20261027/proof-queue.json').write_text(json.dumps(q,indent=2)+'\n')
m='PV_L2B_Cursor'
initial='''import PV_L2B_Rejection
set_option autoImplicit false
namespace PV_L2B_Cursor
-- Absolute consumed-word cursor; initial source word=8 triggers the first refill.
def offset (consumed : Nat) : Nat := 4*(consumed % 8)
def blockIndex (consumed : Nat) : Nat := consumed/8
def afterWord (consumed : Nat) : Nat := consumed%8+1
def consumed (rejections : List Nat) : Nat := (rejections.map (fun r => r+1)).sum
end PV_L2B_Cursor
'''
def cursor(body,names):add(body,names,m,initial=initial if not any(i['module']==m for i in q) else None)
cursor('theorem offset_zero : offset 0 = 0 := rfl','offset_zero')
cursor('theorem offset_bound (n : Nat) : offset n < 32 := by unfold offset; have := Nat.mod_lt n (by decide : 0<8); omega','offset_bound')
cursor('theorem last_byte_bound (n : Nat) : offset n + 3 < 32 := by unfold offset; have := Nat.mod_lt n (by decide : 0<8); omega','last_byte_bound')
cursor('theorem read_word_bound (n : Nat) : afterWord n ≤ 8 := by unfold afterWord; have := Nat.mod_lt n (by decide : 0<8); omega','read_word_bound')
cursor('theorem read_word_positive (n : Nat) : 0 < afterWord n := by unfold afterWord; omega','read_word_positive')
cursor('theorem offset_period (n : Nat) : offset (n+8) = offset n := by simp [offset,Nat.add_mod]','offset_period')
cursor('theorem block_step (n : Nat) : blockIndex (n+8) = blockIndex n+1 := by simp [blockIndex,Nat.add_div_right]','block_step')
cursor('theorem word_period (n : Nat) : afterWord (n+8) = afterWord n := by simp [afterWord,Nat.add_mod]','word_period')
cursor('theorem absolute_decomposition (n : Nat) : n = 8*blockIndex n+n%8 := by unfold blockIndex; omega','absolute_decomposition')
cursor('theorem refill_iff (n : Nat) : afterWord n = 8 ↔ n%8=7 := by unfold afterWord; omega','refill_iff')
cursor('theorem first_limb_offset (r : Nat) : offset (r+1) = 4*((r+1)%8) := rfl','first_limb_offset')
cursor('theorem accepted_no_rejection_next : offset 1 = 4 := rfl','accepted_no_rejection_next')
cursor('theorem one_rejection_next : offset 2 = 8 := rfl','one_rejection_next')
cursor('theorem cursor_nil : consumed [] = 0 := rfl','cursor_nil')
cursor('theorem cursor_cons (r : Nat) (rs : List Nat) : consumed (r::rs) = r+1+consumed rs := by simp [consumed]','cursor_cons')
cursor('theorem cursor_append (rs ts : List Nat) : consumed (rs++ts) = consumed rs+consumed ts := by simp [consumed,List.sum_append]','cursor_append')
cursor('theorem cursor_rejection_sum (rs : List Nat) : consumed rs = rs.sum+rs.length := by\n  induction rs with\n  | nil => rfl\n  | cons r rs ih => simp only [cursor_cons,List.sum_cons,List.length_cons]; rw [ih]; omega','cursor_rejection_sum')
cursor('theorem qm31_cursor (a b c d : Nat) : consumed [a,b,c,d] = a+b+c+d+4 := by simp [consumed]; omega','qm31_cursor')
cursor('theorem qm31_consumption_bound (a b c d : Nat) (ha : a<16) (hb : b<16) (hc : c<16) (hd : d<16) : consumed [a,b,c,d] ≤ 64 := by rw [qm31_cursor]; omega','qm31_consumption_bound')
cursor('theorem cap_cursor_independent {A B : Type} (f : A → B) (n : Nat) (xs : List (Option A)) : offset (PV_L2B_Rejection.scan n (xs.map (Option.map f))).1 = offset (PV_L2B_Rejection.scan n xs).1 := by rw [PV_L2B_Rejection.count_map]','cap_cursor_independent')
pathlib.Path('evidence/pv-l2b-20261027/proof-queue.json').write_text(json.dumps(q,indent=2)+'\n')
m='PV_L2B_Guards'
initial='''import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
set_option autoImplicit false
namespace PV_L2B_Guards
-- Mathematical guard laws. Native builder/canonicality/refinement association
-- is retained, never represented by an additional trust item.
def firstFailure : List Bool → Nat
 | [] => 0
 | true :: _ => 1
 | false :: xs => 1+firstFailure xs
end PV_L2B_Guards
'''
def guard(body,names):add(body,names,m,initial=initial if not any(i['module']==m for i in q) else None)
guard('theorem passing_trace (n : Nat) : firstFailure (List.replicate n false) = n := by\n  induction n with\n  | zero => rfl\n  | succ n ih => simp [List.replicate_succ,firstFailure,ih]; omega','passing_trace')
guard('theorem failed_trace (xs : List Bool) : firstFailure (true::xs) = 1 := rfl','failed_trace')
guard('theorem zero_guard {A : Type} [Zero A] [DecidableEq A] (x : A) (hx : x=0) : decide (x ≠ 0) = false := by simp [hx]','zero_guard')
guard('theorem equality_guard {A : Type} [DecidableEq A] (x y : A) (h : x=y) : decide (x ≠ y) = false := by simp [h]','equality_guard')
guard('theorem active_zero_guard {A : Type} [Zero A] [DecidableEq A] (active : Bool) (x : A) (h : active=true → x=0) : (active && decide (x ≠ 0)) = false := by\n  cases active <;> simp_all','active_zero_guard')
guard('theorem canonical_guard (p x : Nat) (hx : x<p) : decide (p≤x) = false := by simp; omega','canonical_guard')
guard('theorem modular_canonical (p a b : Nat) (hp : 0<p) : (a+b)%p<p := Nat.mod_lt _ hp','modular_canonical')
guard('theorem zmod_canonical (p : Nat) [NeZero p] (x : ZMod p) : x.val<p := ZMod.val_lt x','zmod_canonical')
guard('theorem balanced_dependent {A : Type} [AddGroup A] (sum : A) : sum+(-sum)=0 := add_neg_cancel sum','balanced_dependent')
guard('theorem balanced_dependent_first {A : Type} [AddGroup A] (sum : A) : (-sum)+sum=0 := neg_add_cancel sum','balanced_dependent_first')
guard('''theorem inactive_balance {I A : Type} [Fintype I] [DecidableEq I] [AddCommGroup A]
    (d : I) (v : I → A) :
    (∑ i : I, if i=d then -(∑ j in Finset.univ.erase d, v j) else v i)=0 := by
  classical
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ d)]
  simp only [ite_true]
  have hs : (∑ i in Finset.univ.erase d, if i=d then -(∑ j in Finset.univ.erase d, v j) else v i) = ∑ i in Finset.univ.erase d, v i := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_erase] at hi
    simp [hi.1]
  rw [hs]; exact neg_add_cancel _''','inactive_balance')
guard('''theorem padding_total {I A : Type} [Fintype I] [AddCommGroup A]
    (active : I → Bool) (padding : I → A)
    (hz : ∀ i, active i=true → padding i=0)
    (hs : (∑ i : I, if active i then 0 else padding i)=0) :
    (∑ i : I, padding i)=0 := by
  classical
  have h : (∑ i : I, padding i) = ∑ i : I, if active i then 0 else padding i := by
    apply Finset.sum_congr rfl
    intro i hi
    cases ha : active i <;> simp [ha,hz i ha]
  exact h.trans hs''','padding_total')
guard('''theorem padding_preserves_sum {I A : Type} [Fintype I] [AddCommGroup A]
    (helper padding : I → A) (hh : (∑ i : I, helper i)=0)
    (hp : (∑ i : I, padding i)=0) :
    (∑ i : I, helper i+padding i)=0 := by rw [Finset.sum_add_distrib,hh,hp,add_zero]''','padding_preserves_sum')
guard('theorem paired_helper_cancels {I A : Type} [Fintype I] [AddCommGroup A] (v : I → A) : (∑ i : I, v i) - (∑ i : I, v i) = 0 := sub_self _','paired_helper_cancels')
guard('theorem c1_count_guard (count : Nat) (h : count=16) : decide (count ≠ 16)=false := by simp [h]','c1_count_guard')
guard('theorem mask_count_guard (count : Nat) (h : count=10) : decide (count ≠ 10)=false := by simp [h]','mask_count_guard')
guard('theorem audit_shortcircuit (a b c d e : Bool) (ha : a=false) (hb : b=false) (hc : c=false) (hd : d=false) (he : e=false) : a || b || c || d || e = false := by simp [ha,hb,hc,hd,he]','audit_shortcircuit')
guard('theorem helper_option_guard {A : Type} [Zero A] [DecidableEq A] (v : Option A) (h : v=some 0) : decide (v ≠ some 0)=false := by simp [h]','helper_option_guard')
guard('''theorem sumcheck_boundary {A : Type} [AddMonoid A] (v0 v1 running p0 p1 : A)
    (interpolation0 : p0=v0) (interpolation1 : p1=v1)
    (initial : v0+v1=running) : p0+p1=running := by rw [interpolation0,interpolation1,initial]''','sumcheck_boundary')
guard('''theorem sumcheck_terminal {A : Type} [DecidableEq A] (oracle running polynomial : A)
    (low_degree_identity : oracle=polynomial) (running_eval : running=polynomial) :
    decide (oracle ≠ running)=false := by simp [low_degree_identity,running_eval]''','sumcheck_terminal')
pathlib.Path('evidence/pv-l2b-20261027/proof-queue.json').write_text(json.dumps(q,indent=2)+'\n')
m='PV_L2B_EntropyTrace'
initial='''import PV_L2B_SamplerLaw
import PV_L2B_Rejection
set_option autoImplicit false
namespace PV_L2B_EntropyTrace
-- Per successful 64-byte fill: 0=first zero (second check skipped),
-- 1=second zero, 2=both nonzero. OS error schedule is a separate input.
def kind {A B : Type} : Option A × Option B → Nat
 | (none, _) => 0
 | (some _, none) => 1
 | (some _, some _) => 2
def checks (kind : Nat) : Nat := if kind=0 then 1 else 2
def branches {A B : Type} : Nat → List (Option A × Option B) → List Nat
 | 0, _ => []
 | _+1, [] => []
 | n+1, x::xs => if kind x=2 then [2] else kind x :: branches n xs
end PV_L2B_EntropyTrace
'''
def ent(body,names):add(body,names,m,initial=initial if not any(i['module']==m for i in q) else None)
ent('theorem first_zero {A B : Type} (b : Option B) : kind ((none : Option A), b)=0 := rfl','first_zero')
ent('theorem second_zero {A B : Type} (a : A) : kind (some a, (none : Option B))=1 := rfl','second_zero')
ent('theorem accepted_pair {A B : Type} (a : A) (b : B) : kind (some a,some b)=2 := rfl','accepted_pair')
ent('''theorem kind_relabel {A B C D : Type} (f : A → C) (g : B → D) (p : Option A × Option B) :
    kind (p.1.map f,p.2.map g)=kind p := by
  rcases p with ⟨a,b⟩; cases a <;> cases b <;> rfl''','kind_relabel')
ent('''theorem branches_relabel {A B C D : Type} (f : A → C) (g : B → D)
    (n : Nat) (xs : List (Option A × Option B)) :
    branches n (xs.map (fun p => (p.1.map f,p.2.map g)))=branches n xs := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih =>
    cases xs with
    | nil => rfl
    | cons x xs => simp only [List.map_cons,branches,kind_relabel,ih]''','branches_relabel')
ent('theorem first_skips_second : checks 0=1 := rfl','first_skips_second')
ent('theorem second_checks_both : checks 1=2 := rfl','second_checks_both')
ent('theorem success_checks_both : checks 2=2 := rfl','success_checks_both')
ent('''theorem full_comparison_count_relabel {A B C D : Type} (f : A → C) (g : B → D)
    (n : Nat) (xs : List (Option A × Option B)) :
    ((branches n (xs.map (fun p => (p.1.map f,p.2.map g)))).map checks).sum =
      ((branches n xs).map checks).sum := by rw [branches_relabel]''','full_comparison_count_relabel')
ent('theorem first_reject_conditional (z : ℚ) (hz : z ≠ 0) (ht : 2-z ≠ 0) : z/(z+(1-z)*z) = 1/(2-z) := by field_simp; ring','first_reject_conditional')
ent('theorem second_reject_conditional (z : ℚ) (hz : z ≠ 0) (ht : 2-z ≠ 0) : ((1-z)*z)/(z+(1-z)*z) = (1-z)/(2-z) := by field_simp; ring','second_reject_conditional')
ent('theorem conditional_class_total (z : ℚ) (ht : 2-z ≠ 0) : 1/(2-z)+(1-z)/(2-z)=1 := by field_simp; ring','conditional_class_total')
pathlib.Path('evidence/pv-l2b-20261027/proof-queue.json').write_text(json.dumps(q,indent=2)+'\n')

q.sort(key=lambda i: ["PV_L2B_Rejection","PV_L2B_SamplerLaw","PV_L2B_Cursor","PV_L2B_EntropyTrace","PV_L2B_Guards"].index(i["module"]))
pathlib.Path("evidence/pv-l2b-20261027/proof-queue.json").write_text(json.dumps(q,indent=2)+"\n")
m='PV_L2B_JointTransport'
initial='''import PV_L2B_Rejection
import PV_L2B_Cursor
import PV_L2B_EntropyTrace
import PV_L2B_Guards
set_option autoImplicit false
namespace PV_L2B_JointTransport
end PV_L2B_JointTransport
'''
def joint(body,names):add(body,names,m,initial=initial if not any(i['module']==m for i in q) else None)
joint('''theorem rejection_cursor_joint {A B : Type} (f : A → B) (n : Nat) (xs : List (Option A)) :
    (PV_L2B_Rejection.trace n (xs.map (Option.map f)),
      PV_L2B_Cursor.offset (PV_L2B_Rejection.scan n (xs.map (Option.map f))).1) =
    (PV_L2B_Rejection.trace n xs, PV_L2B_Cursor.offset (PV_L2B_Rejection.scan n xs).1) := by
  rw [PV_L2B_Rejection.trace_relabel,PV_L2B_Rejection.count_map]''','rejection_cursor_joint')
joint('''theorem constant_guard_joint {View Trace : Type} (v w : View) (tv tw : Trace)
    (hv : v=w) (ht : tv=tw) (checks : Nat) :
    (v,tv,PV_L2B_Guards.firstFailure (List.replicate checks false)) = (w,tw,checks) := by
  rw [hv,ht,PV_L2B_Guards.passing_trace]''','constant_guard_joint')
joint('''theorem outside_existing_event {I O : Type} (real sim : I → O) (bad : I → Prop)
    (agreement : ∀ i, ¬ bad i → real i=sim i) (i : I) :
    real i ≠ sim i → bad i := by
  intro h; by_contra hb; exact h (agreement i hb)''','outside_existing_event')
joint('''theorem weighted_joint_transport {I O : Type} [Fintype I]
    (weight : I → ℚ) (real sim : I → O) (test : O → ℚ)
    (same : ∀ i, real i=sim i) :
    (∑ i : I, weight i*test (real i)) = ∑ i : I, weight i*test (sim i) := by
  apply Finset.sum_congr rfl
  intro i hi; rw [same i]''','weighted_joint_transport')
pathlib.Path('evidence/pv-l2b-20261027/proof-queue.json').write_text(json.dumps(q,indent=2)+'\n')

# Check the cursor initializer with its first bounds theorem in one focused target.
first=next(i for i in q if i['module']=='PV_L2B_Cursor')
second=q[q.index(first)+1]
second['initial']=first['initial'].replace('end PV_L2B_Cursor',first['body']+'\n#print axioms offset_zero\nend PV_L2B_Cursor')
q.remove(first)
pathlib.Path('evidence/pv-l2b-20261027/proof-queue.json').write_text(json.dumps(q,indent=2)+'\n')
