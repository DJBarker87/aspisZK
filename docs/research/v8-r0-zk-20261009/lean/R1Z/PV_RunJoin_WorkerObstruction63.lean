import R1Z.PV_RunJoin_ResultPost41
import R1Z.ProverRwFullFuns
/-! Residual-dictionary diagnostic only. Existential success on an unrelated
worker input need not imply success at the caller's public scheduling hint. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_WorkerObstruction63
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_ResultPost41
variable [ExternalTypes]

def sparse (ops : ExternalFuns) : ExternalFuns :=
  {ops with op257 := fun {_ _} _ cost _ _ =>
    if cost=0#usize then ok ⟨[],by simp⟩ else .div}

theorem some_input (ops : ExternalFuns) {T F : Type}
    (inst : core.ops.function.Fn F Usize T) (f : F) :
    ∃ out, @host_work.map _ (sparse ops) T F inst 0#usize 0#usize f=ok out := by
  refine ⟨⟨[],by simp⟩,?_⟩
  simp only [host_work.map,sparse,ite_true]

/-- A successful request exists for every supplied callback, but the actual
commitment caller uses 200, at which this dictionary diverges for every count. -/
theorem denied (ops : ExternalFuns) {T F : Type}
    (inst : core.ops.function.Fn F Usize T) (count : Usize) (f : F) :
    @host_work.map _ (sparse ops) T F inst 200#usize count f=.div := by
  change (if (200#usize : Usize)=0#usize then _ else _)=_
  rw [if_neg (by decide)]

variable [ExternalFuns]
def Denied : Prop := ∀ {T F : Type} (inst : core.ops.function.Fn F Usize T)
    (count : Usize) (f : F), host_work.map inst 200#usize count f=.div

theorem encode (denied : Denied) (domain : host_commitment.EncodingDomain)
    (messages : Slice (Array aspis_core.field.wide_exact.WideExact 1024#usize))
    (variant : transport.Variant) (lanes : Slice Usize) :
    Post (fun status => match status with | .Err _ => True | .Ok _ => False)
      (host_commitment.encode_commitment_words domain messages variant lanes) := by
  unfold host_commitment.encode_commitment_words
  apply PV_RunJoin_ResultPost41.bind
  rintro ⟨reserved,words⟩
  apply PV_RunJoin_ResultPost41.bind
  intro mapped
  cases mapped with
  | Err e => trivial
  | Ok unit =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
    apply PV_RunJoin_ResultPost41.bind
    intro checked
    cases checked with
    | Err e => trivial
    | Ok unit =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,denied,bind_tc_div]
      trivial

#print axioms sparse
#print axioms some_input
#print axioms denied
#print axioms Denied
#print axioms encode
end R1Z.PV_RunJoin_WorkerObstruction63
