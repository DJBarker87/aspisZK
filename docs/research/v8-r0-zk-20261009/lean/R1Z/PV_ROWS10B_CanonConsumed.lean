import Aeneas
set_option autoImplicit false
namespace R1Z.PV_ROWS10B_CanonConsumed
open Aeneas Aeneas.Std
/-- Abstract QM31 carrier with the actual four extracted U32 limbs. The
skeleton specializes to the current extracted QM31 without changing carriers. -/
def Canonical {Q : Type} (limb : Q → Fin 4 → U32) (q : Q) : Prop :=
  ∀ i, (limb q i).val < 2147483647

def Coefficients {Q : Type} (limb : Q → Fin 4 → U32)
    (p : Array Q 28#usize) : Prop := ∀ x ∈ p.val, Canonical limb x

structure Event (Q Trace State : Type) where
  values : Array Q 28#usize
  coefficients : Array Q 28#usize
  point : Array Q 10#usize
  updated : Array Q 10#usize
  round : Usize
  trace : Trace
  after : State
  sampled : Q
  read : Q

variable {Q Trace State E : Type}

def PV_ROWS10B_Link_CallerPrefix
    (reached : Array Q 28#usize → Q → Prop) (occurs : Event Q Trace State → Prop) : Prop :=
  ∀ p q, reached p q → ∃ e, occurs e ∧ e.coefficients = p ∧ e.read = q

def PV_ROWS10B_Link_PrefixEquations (occurs : Event Q Trace State → Prop)
    (interpolate : Array Q 28#usize → Result (Array Q 28#usize))
    (semantic : Trace → Result ((core.result.Result Q E) × State)) : Prop :=
  ∀ e, occurs e →
    interpolate e.values = .ok e.coefficients ∧
    semantic e.trace = .ok (.Ok e.sampled, e.after) ∧
    Array.update e.point e.round e.sampled = .ok e.updated ∧
    Array.index_usize e.updated e.round = .ok e.read

def PV_ROWS10B_Link_RoundRange (occurs : Event Q Trace State → Prop) : Prop :=
  ∀ e, occurs e → e.round.val < 10

def PV_ROWS10B_Link_Interpolation (limb : Q → Fin 4 → U32)
    (interpolate : Array Q 28#usize → Result (Array Q 28#usize)) : Prop :=
  ∀ values p, interpolate values = .ok p → Coefficients limb p

def PV_ROWS10B_Link_Semantic (limb : Q → Fin 4 → U32)
    (semantic : Trace → Result ((core.result.Result Q E) × State)) : Prop :=
  ∀ trace q after, semantic trace = .ok (.Ok q, after) → Canonical limb q

/-- Direct Aeneas array-library proof; no project callback dictionary is used. -/
theorem update_read {n : Usize} (xs ys : Array Q n) (i : Usize) (q z : Q)
    (inside : i.val < n.val)
    (updated : Array.update xs i q = .ok ys)
    (readback : Array.index_usize ys i = .ok z) : z = q := by
  have hx : i.val < xs.val.length := by rw [xs.property]; exact inside
  obtain ⟨out, ho, hset⟩ := WP.spec_imp_exists (Array.update_spec xs i q hx)
  rw [ho] at updated
  cases updated
  subst ys
  have hy : i.val < (xs.set i q).val.length := by rw [(xs.set i q).property]; exact inside
  obtain ⟨value, hv, helement⟩ := WP.spec_imp_exists (Array.index_usize_spec (xs.set i q) i hy)
  rw [hv] at readback
  have hz : value = z := Result.ok.inj readback
  rw [← hz, helement]
  change (xs.val.set i.val q)[i.val]'((by simpa only [List.length_set] using hx)) = q
  exact List.getElem_set_self hx

/-- Top-down V403 consumed domain; no canonicality premise occurs in the
native reachability link or in the computational prefix event itself. -/
theorem consumed (limb : Q → Fin 4 → U32)
    (reached : Array Q 28#usize → Q → Prop) (occurs : Event Q Trace State → Prop)
    (interpolate : Array Q 28#usize → Result (Array Q 28#usize))
    (semantic : Trace → Result ((core.result.Result Q E) × State))
    (caller : PV_ROWS10B_Link_CallerPrefix reached occurs)
    (prefixEq : PV_ROWS10B_Link_PrefixEquations occurs interpolate semantic)
    (range : PV_ROWS10B_Link_RoundRange occurs)
    (polynomial : PV_ROWS10B_Link_Interpolation limb interpolate)
    (challenge : PV_ROWS10B_Link_Semantic limb semantic) :
    ∀ p q, reached p q → Coefficients limb p ∧ Canonical limb q := by
  intro p q hit
  obtain ⟨e, he, hp, hq⟩ := caller p q hit
  obtain ⟨hi, hs, hu, hr⟩ := prefixEq e he
  rw [← hp, ← hq]
  refine ⟨polynomial e.values e.coefficients hi, ?_⟩
  have same := update_read e.point e.updated e.round e.sampled e.read (range e he) hu hr
  rw [same]
  exact challenge e.trace e.sampled e.after hs
#print axioms update_read
#print axioms consumed
end R1Z.PV_ROWS10B_CanonConsumed
