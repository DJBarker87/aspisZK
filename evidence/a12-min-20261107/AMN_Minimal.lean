/-
AMN_Minimal: the minimal A1/A2 obligation the split-B top actually consumes,
in TAS stand-in form.  Target not yet established.  Core Lean plus RSL_,
TCK_WeakRoot0, TAS_Interfaces and AMN_ReturnedPath.  No sorry, no axiom, no
new hypothesis about the actual code.

Where native1/native2 occur in the top (AMN_REPORT.md section 1 quotes each):
  * accepted1 / accepted2 (S2W_D189Wrappers.first/second = ok (.Ok ..)) at the
    ONE selected occurrence each (NNE_A3/NNE_A4);
  * game (d), through CPG_RuntimeTrace.Step.invoke and CPP_Invocation.native:
    the `.first` arm is `firstEffect store call (first native1 ..)`, which
    commits iff the reply is `.ok (.Ok (saved,_,_))` and rolls back on every
    other reply (`| _ => (store,.rollback,.inl reply)`); the `.second` arm is
    `(store,.rollback,.inr (second native2 ..))`, whose reply Step never reads
    (Step uses `.1` and `.2.1` only);
  * queries (L154): `ARW_Induced.issued native1 ..` only branches on whether
    `first native1 ..` at the adversary's first output is `.ok (.Ok ..)`;
  * the charged events E_head / E_rec: definitions over native1 := model1, no
    native2, no actual-code obligation.
Consequences:
  * A2 is needed ONLY in the Ok direction, ONLY at the selected TX2 occurrence
    (`Sel2`).  Err and abort directions of native2 are never inspected.
  * A1 is needed at EVERY stage1 invocation of both traces (game (d)), with the
    exact Ok bytes (commit writes `saved`) and, on a returned Err, only that the
    model does not reply Ok (any error, any payload: `NotOk1`).  Aborts are not
    an A1 obligation: NNE_ stamps the abort indicator (ruling (bo)); see the
    RZ-STATE caveat in AMN_REPORT.md section 1.4.
  * Error payloads, log lines, event chronology and error formatting are never
    inspected by any consumer.

`MinSig` holds the four model-outcome stand-ins.  `withMin S M` is the TAS
`Sig` whose ModelRet1/ModelRet2 are built from them; NNE_AcceptanceSig.physical
is exactly of this shape (host instantiation in AMN_REPORT.md section 3).
-/
import TAS_Interfaces
import AMN_ReturnedPath
set_option autoImplicit false

namespace RSL.AMN
open RSL.TAS
open TX2_241 (V2Lib)
open TX1_345 (S1Lib)

/-- Model-outcome stand-ins.  Host terms (NNE_AcceptanceSig.physical, Data d):
  * `Ok1 c a b`  := ∀ e p data, a = child1 d.err e p data → ∀ saved,
      b = nativeBytes saved → d.native1 (S.model1 c) p e.first data = ok (.Ok saved);
  * `NotOk1 c a` := ∀ e p data, a = child1 d.err e p data →
      ∃ pe, d.native1 (S.model1 c) p e.first data = ok (.Err pe)
      (NNE_Stage1Error consumes exactly this; the weaker
      `≠ ok (.Ok _)` would also suffice for firstEffect's rollback arm);
  * `Sel2 c a`   := a = child2 d.err (d.e2 c) (d.program c) (d.data2 c) (S.env2 c).clock;
  * `Ok2 c a`    := d.native2 (S.model2 c) (d.program c) ((d.e2 c).second secondSizes)
      (d.data2 c) (d.slot c) = ok (.Ok ()). -/
structure MinSig (S : Sig) where
  Ok1 : S.Ctx → TX1_345.Args → Bytes → Prop
  NotOk1 : S.Ctx → TX1_345.Args → Prop
  Sel2 : S.Ctx → TX2_241.Args → Prop
  Ok2 : S.Ctx → TX2_241.Args → Prop

/-- The TAS signature with ModelRet built from the minimal stand-ins. -/
def withMin (S : Sig) (M : MinSig S) : Sig :=
  { S with
    ModelRet1 := fun c a r => (∀ b, r = .ok b → M.Ok1 c a b) ∧ (∀ e, r = .error e → M.NotOk1 c a)
    ModelRet2 := fun c a r => M.Sel2 c a → r = .ok () → M.Ok2 c a }

section
variable (S : Sig) (M : MinSig S) (L : PoolLib) (D : DeployedIds) (V0 : V2Lib)
  (VL : VLib) (P : PreparedNew VL) (C : S1Lib VL)

/-- Minimal A1: every RETURNED arm of the canonical 345 reference, at an
environment agreeing with the runtime oracles, is reproduced by model1: Ok with
the same bytes, Err as some Err.  Universally quantified over the arguments,
because game (d) inspects every stage1 invocation. -/
structure A1min where
  ok : ∀ c a env o b, S.Exhibited c → S.EnvRep c env →
    TX1_345.Ref VL P C a env o → o.exit = .ret (.ok b) → M.Ok1 c a b
  err : ∀ c a env o e, S.Exhibited c → S.EnvRep c env →
    TX1_345.Ref VL P C a env o → o.exit = .ret (.error e) → M.NotOk1 c a

/-- Minimal A2: only the returned-Ok arm of the canonical 241 reference, only at
the selected TX2 occurrence. -/
structure A2min where
  ok : ∀ c a env o, S.Exhibited c → S.EnvRep c env → M.Sel2 c a →
    TX2_241.Ref L D V0 a env o → o.exit = .ret (.ok ()) → M.Ok2 c a

/-- Sufficiency: the minimal A1 inhabits the exact TAS field. -/
def toNND_A1 (h : A1min S M VL P C) : NND_A1 (withMin S M) VL P C where
  stage1 := by
    intro c a env o r hx he href hret
    refine ⟨fun b hb => ?_, fun e he' => ?_⟩
    · subst hb; exact h.ok c a env o b hx he href hret
    · subst he'; exact h.err c a env o e hx he href hret

/-- Sufficiency: the minimal A2 inhabits the exact TAS field. -/
def toNND_A2 (h : A2min S M L D V0) : NND_A2 (withMin S M) L D V0 where
  stage2 := by
    intro c a env o r hx he href hret hsel hr
    subst hr
    exact h.ok c a env o hx he hsel href hret

/-- At a `withMin` signature (the shape of NNE's physical Sig) the TAS field IS
the minimal obligation: nothing beyond A2min is ever demanded there. -/
def ofNND_A2 (h : NND_A2 (withMin S M) L D V0) : A2min S M L D V0 where
  ok := fun c a env o hx he hsel href hret => h.stage2 c a env o _ hx he href hret hsel rfl

def ofNND_A1 (h : NND_A1 (withMin S M) VL P C) : A1min S M VL P C where
  ok := fun c a env o b hx he href hret => (h.stage1 c a env o _ hx he href hret).1 b rfl
  err := fun c a env o e hx he href hret => (h.stage1 c a env o _ hx he href hret).2 e rfl

/-- The Err arm of ModelRet2 is vacuous: A2's Err direction is never consumed. -/
theorem modelRet2_error_vacuous (c : S.Ctx) (a : TX2_241.Args) (e : ProgramError) :
    (withMin S M).ModelRet2 c a (.error e) := by
  intro _ h
  cases h

/-- Teeth: the Ref-quantified form forces returned-determinism of the reference
on the Ok arm wherever the model outcome is functional.  So A1 is unprovable if
some library leaf law on a returned path is relational (two Ok values at the
SAME arguments and environment); the worker must check each leaf law first. -/
theorem a1_forces_det (h : A1min S M VL P C)
    (func : ∀ c a b b', M.Ok1 c a b → M.Ok1 c a b' → b = b')
    (c : S.Ctx) (a : TX1_345.Args) (env : Env) (hx : S.Exhibited c) (he : S.EnvRep c env)
    (o o' : Obs (Except ProgramError Bytes)) (b b' : Bytes)
    (r : TX1_345.Ref VL P C a env o) (r' : TX1_345.Ref VL P C a env o')
    (k : o.exit = .ret (.ok b)) (k' : o'.exit = .ret (.ok b')) : b = b' :=
  func c a b b' (h.ok c a env o b hx he r k) (h.ok c a env o' b' hx he r' k')

/-- Route R1, formalised ("two functions satisfying the same functional spec
agree").  For ANY observation function `g` (the lifted model, or the actual
I.f241): membership of `g` in the reference, returned-determinism of the
reference, LIVENESS of `g` where the reference returns, and the representation
of `g`'s Ok as the model's Ok give A2min.  Liveness is not implied by
membership (AMN.alloc_admits_both). -/
def transfer2 (g : TX2_241.Args → Env → Obs (Except ProgramError Unit))
    (det : ∀ c a env o o' x x', S.Exhibited c → S.EnvRep c env → M.Sel2 c a →
      TX2_241.Ref L D V0 a env o → TX2_241.Ref L D V0 a env o' →
      o.exit = .ret x → o'.exit = .ret x' → x = x')
    (mem : ∀ c a env, S.Exhibited c → S.EnvRep c env → M.Sel2 c a →
      TX2_241.Ref L D V0 a env (g a env))
    (live : ∀ c a env o x, S.Exhibited c → S.EnvRep c env → M.Sel2 c a →
      TX2_241.Ref L D V0 a env o → o.exit = .ret x → ∃ y, (g a env).exit = .ret y)
    (rep : ∀ c a env, S.Exhibited c → S.EnvRep c env → M.Sel2 c a →
      (g a env).exit = .ret (.ok ()) → M.Ok2 c a) :
    A2min S M L D V0 where
  ok := by
    intro c a env o hx he hsel href hret
    obtain ⟨y, hy⟩ := live c a env o _ hx he hsel href hret
    have hyx := det c a env (g a env) o y (.ok ()) hx he hsel (mem c a env hx he hsel) href hy hret
    subst hyx
    exact rep c a env hx he hsel hy

/-- Route R1 for A1 (Ok bytes and Err class). -/
def transfer1 (g : TX1_345.Args → Env → Obs (Except ProgramError Bytes))
    (det : ∀ c a env o o' x x', S.Exhibited c → S.EnvRep c env →
      TX1_345.Ref VL P C a env o → TX1_345.Ref VL P C a env o' →
      o.exit = .ret x → o'.exit = .ret x' → x = x')
    (mem : ∀ c a env, S.Exhibited c → S.EnvRep c env → TX1_345.Ref VL P C a env (g a env))
    (live : ∀ c a env o x, S.Exhibited c → S.EnvRep c env →
      TX1_345.Ref VL P C a env o → o.exit = .ret x → ∃ y, (g a env).exit = .ret y)
    (repOk : ∀ c a env b, S.Exhibited c → S.EnvRep c env →
      (g a env).exit = .ret (.ok b) → M.Ok1 c a b)
    (repErr : ∀ c a env e, S.Exhibited c → S.EnvRep c env →
      (g a env).exit = .ret (.error e) → M.NotOk1 c a) :
    A1min S M VL P C where
  ok := by
    intro c a env o b hx he href hret
    obtain ⟨y, hy⟩ := live c a env o _ hx he href hret
    have hyx := det c a env (g a env) o y (.ok b) hx he (mem c a env hx he) href hy hret
    subst hyx
    exact repOk c a env b hx he hy
  err := by
    intro c a env o e hx he href hret
    obtain ⟨y, hy⟩ := live c a env o _ hx he href hret
    have hyx := det c a env (g a env) o y (.error e) hx he (mem c a env hx he) href hy hret
    subst hyx
    exact repErr c a env e hx he hy

/-- RECOMMENDED route (the NND_Returned shape).  A pure evaluator `val` of the
reference with `NND_Returned.Returns (Ref a) env (val a env)` (every returned
arm equals `val`), plus the model's Ok at `val = .ok ()`, gives A2min.  No
liveness premise: the model is evaluated directly from `val`, and only on the
Ok value.  NND_Stage2Eval.value / .returned is this `val` / `ret` for 241,
parameterized by NND_PoolValues.Values and NND_Tx2Values.Values. -/
def viaReturns2 (val : TX2_241.Args → Env → Except ProgramError Unit)
    (ret : ∀ c a env, S.Exhibited c → S.EnvRep c env → M.Sel2 c a →
      ∀ o r, TX2_241.Ref L D V0 a env o → o.exit = .ret r → r = val a env)
    (okT : ∀ c a env, S.Exhibited c → S.EnvRep c env → M.Sel2 c a →
      val a env = .ok () → M.Ok2 c a) :
    A2min S M L D V0 where
  ok := fun c a env o hx he hsel href hret =>
    okT c a env hx he hsel (ret c a env hx he hsel o _ href hret).symm

/-- Recommended route for A1: evaluator with Returns (NND_Stage1RefEval.value /
.returned, parameterized by NND_Tx1ReturnedValues.Values), the model's exact Ok
at an Ok value, and only SOME model Err at an Err value. -/
def viaReturns1 (val : TX1_345.Args → Env → Except ProgramError Bytes)
    (ret : ∀ c a env, S.Exhibited c → S.EnvRep c env →
      ∀ o r, TX1_345.Ref VL P C a env o → o.exit = .ret r → r = val a env)
    (okT : ∀ c a env b, S.Exhibited c → S.EnvRep c env → val a env = .ok b → M.Ok1 c a b)
    (errT : ∀ c a env e, S.Exhibited c → S.EnvRep c env → val a env = .error e → M.NotOk1 c a) :
    A1min S M VL P C where
  ok := fun c a env o b hx he href hret =>
    okT c a env b hx he (ret c a env hx he o _ href hret).symm
  err := fun c a env o e hx he href hret =>
    errT c a env e hx he (ret c a env hx he o _ href hret).symm

end

#print axioms toNND_A1
#print axioms toNND_A2
#print axioms ofNND_A1
#print axioms ofNND_A2
#print axioms modelRet2_error_vacuous
#print axioms a1_forces_det
#print axioms transfer2
#print axioms transfer1
#print axioms viaReturns2
#print axioms viaReturns1

end RSL.AMN
