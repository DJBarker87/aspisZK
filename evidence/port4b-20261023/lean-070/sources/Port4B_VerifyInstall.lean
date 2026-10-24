import Port4B_TailReads

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4B_VerifyInstall
open Aeneas Aeneas.Std Result
open MultiproofConeRef
open Port3_NativeBatchCalls (Indices Values)

def digest {X : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 X) :
    MultiproofConeRef.aspis_core.digest.Digest32 X := ⟨D.coremarkerCopyInst,D.digest⟩

/-- P6 binary verifier owned-carrier lowering, preserving returned scratch.
No whole-verifier output/log agreement is a field of this installation. -/
def verify {X : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 X) (hash : X)
    (arity : Port3_NativeBatchBody.multiproof.Arity) (root : Array U8 32#usize)
    (idx : Indices) (val : Values) (n : Usize) (nodes : Slice U8) :
    Result (Bool × Indices × Values) := do
  match arity with
  | .Two =>
    let (accepted,out) ← reference.verify_owned (digest D) hash root ⟨idx,val,n,0#usize⟩ nodes
    ok (accepted,out.idx,out.val)
  | .Eight => fail .panic

def install (base : Port3_NativeBatchBody.Ops) : Port3_NativeBatchBody.Ops :=
  {Port4B_SlotInstall.install base with op10:=verify}

theorem normalization {X : Type} (D : MultiproofConeRef.aspis_core.digest.Digest32 X) (hash : X)
    (root : Array U8 32#usize) (s : reference.Scratch) (nodes : Slice U8) :
    MultiproofConeP6Verify.wrapper (fun s => reference.levels D hash s nodes 18#u32) root s nodes=
      reference.verify_owned D hash root s nodes := rfl

theorem read_zero {T : Type} [Inhabited T] (a : Array T 16#usize) (value : T)
    (read : Array.index_usize a 0#usize=ok value) : a.val[0]! = value := by
  have len : a.val.length=16 := a.property
  have looked := List.getElem?_eq_getElem (show 0<a.val.length by omega)
  simp only [Array.index_usize,Array.getElem?_Usize_eq,show (0#usize).val=0 from rfl,looked] at read
  exact (getElem!_pos _ _ (by omega)).trans (Result.ok.inj read)

theorem compare_true (a b : Array U8 32#usize)
    (read : core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 a b=ok true) : a=b := by
  simpa only [MultiproofConeLeaf.digest_eq_total,Result.ok.injEq,decide_eq_true_eq] using read

/-- Accepted owned wrapper itself forces the height return and physical final
root/cursor guards; no independently successful height run is supplied. -/
theorem wrapper_success (run : reference.Scratch → Result reference.Level)
    (root : Array U8 32#usize) (s out : reference.Scratch) (nodes : Slice U8)
    (accepted : MultiproofConeP6Verify.wrapper run root s nodes=ok (true,out)) :
    run {s with «at»:=0#usize}=ok (.Done out) ∧
    MultiproofConeRootGuard.sourceRoot root nodes out=true := by
  unfold MultiproofConeP6Verify.wrapper at accepted
  repeat' first
  | (solve | cases accepted)
  | uncase_result
  | head_reduce accepted
  | split at accepted
  all_goals
    have pair := Result.ok.inj accepted
    have cursor := congrArg Prod.fst pair
    have state := congrArg Prod.snd pair
    dsimp only at state cursor
    subst out
    subst_vars
    refine ⟨by assumption,?_⟩
    simp only [MultiproofConeRootGuard.sourceRoot,decide_eq_true_eq]
    refine ⟨?_,?_,?_,?_⟩
    · have one : _ = 1#usize := by assumption
      exact congrArg UScalar.val one
    · have zero : Array.index_usize _ 0#usize=ok 0#u32 := by assumption
      exact congrArg UScalar.val (read_zero _ _ zero)
    · exact (read_zero _ _ (by assumption)).trans (compare_true _ _ (by assumption))
    · exact congrArg UScalar.val (of_decide_eq_true cursor)

#print axioms normalization
#print axioms read_zero
#print axioms compare_true
#print axioms wrapper_success
end AspisR1.Port4B_VerifyInstall
end
