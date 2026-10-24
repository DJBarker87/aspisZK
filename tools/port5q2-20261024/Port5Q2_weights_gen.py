from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parents[2];E=R/'evidence/port5q2-20261024';L=R/'docs/research/100bit-spend-path-20261013/lean';s=(E/'reader-helpers/Funs.lean').read_text();a=s.index('def verifier.read_checkpoint_weights_loop.body');b=s.index('/-- [aspis_r1_cost_probe::verifier::read_checkpoint_semantic_alpha]',a)
body=s[a:b].replace('verifier.read_checkpoint_weights','weights').replace('verifier.Reader.k','read')
body=body.replace('def weights_loop.body','def weights_loop.body (read : CheckpointBytes4Sections.ReadK)').replace('def weights_loop\n','def weights_loop (read : CheckpointBytes4Sections.ReadK)\n').replace('def weights\n','def weights (read : CheckpointBytes4Sections.ReadK)\n').replace('weights_loop.body\n      bytes','weights_loop.body read\n      bytes').replace('weights_loop iter','weights_loop read iter').replace('MutAVec.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter\n      Global weights','intoIter weights')
out='''import Port5Q2_ReaderScalar
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port5Q2_ReaderWeights
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2
abbrev K := aspis_core.field.QM31
abbrev Iter := core.slice.iter.IterMut K

def intoIter (weights : alloc.vec.Vec K) : Result (Iter × (Iter → alloc.vec.Vec K)) :=
  ok (⟨weights.deref,0⟩,fun it => ⟨it.slice.val,it.slice.property⟩)
'''+body+'''
/-- Fixed backing bytes are explicit in the CURRENT helper's recursion. -/
def reads (read : CheckpointBytes4Sections.ReadK) (bytes : Slice U8) :
    Nat → Usize → Result (core.result.Result (List K × Usize) verifier.Error)
  | 0, at1 => ok (.Ok ([],at1))
  | n+1, at1 => do
    let (value,out) ← read ⟨bytes,at1⟩
    match value with
    | .Err e => ok (.Err e)
    | .Ok x => do
      let tail ← reads read bytes n out.at
      match tail with
      | .Err e => ok (.Err e)
      | .Ok (xs,last) => ok (.Ok (x::xs,last))

def write (s : Slice K) (start : Nat) : List K → Slice K
  | [] => s
  | x::xs => (write s (start+1) xs).setAtNat start x

def finish (r : Usize × Option (core.result.Result (alloc.vec.Vec K × Usize) verifier.Error) × Iter) :
    Result (core.result.Result (alloc.vec.Vec K × Usize) verifier.Error) :=
  match r.2.1 with
  | none => ok (.Ok (⟨r.2.2.slice.val,r.2.2.slice.property⟩,r.1))
  | some v => ok v

/-- Deferred native iterator backwrites compose in source order; every read
outcome and short circuit is retained. This is a symbolic length induction. -/
theorem loop_exact (read : CheckpointBytes4Sections.ReadK) (bytes : Slice U8)
    (n : Nat) (it : Iter) (back : Iter → Iter) (at1 : Usize)
    (remaining : it.i+n=it.slice.val.length) :
    (do let r ← weights_loop read it back bytes at1; finish r) =
      (do let r ← reads read bytes n at1
          match r with
          | .Err e => ok (.Err e)
          | .Ok (xs,last) =>
            let final := back ⟨write it.slice it.i xs,it.i+n⟩
            ok (.Ok (⟨final.slice.val,final.slice.property⟩,last))) := by
  induction n generalizing it back at1 with
  | zero =>
    have inactive : ¬ it.i < it.slice.len := by change ¬ it.i < it.slice.val.length; omega
    unfold weights_loop
    rw [Aeneas.Std.loop.eq_def]
    simp only [weights_loop.body,core.slice.iter.IteratorIterMut.next,dif_neg inactive,
      bind_tc_ok,Aeneas.Std.uncurry,reads,finish,write,Nat.add_zero]
  | succ n ih =>
    have active : it.i < it.slice.len := by change it.i < it.slice.val.length; omega
    unfold weights_loop
    rw [Aeneas.Std.loop.eq_def]
    simp only [weights_loop.body,core.slice.iter.IteratorIterMut.next,dif_pos active,
      bind_tc_ok,Aeneas.Std.uncurry,reads,bind_assoc_eq]
    generalize called : read ⟨bytes,at1⟩=result
    cases result with
    | fail e => rfl
    | div => rfl
    | ok pair =>
      rcases pair with ⟨value,out⟩
      cases value with
      | Err e => rfl
      | Ok x =>
        try dsimp only
        simp only [Aeneas.Std.uncurry,core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,bind_assoc_eq]
        let it1 : Iter := ⟨it.slice,it.i+1⟩
        let back1 : Iter → Iter := fun im => back {im with slice:=im.slice.setAtNat it.i x}
        change (do let r ← weights_loop read it1 back1 bytes out.at; finish r)=_
        rw [ih it1 back1 out.at (by change it.i+1+n=it.slice.val.length; omega)]
        apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
        intro rest decoded
        cases rest with
        | Err e => rfl
        | Ok pair =>
          rcases pair with ⟨xs,last⟩
          simp only [bind_tc_ok,write]
          have count : it.i+1+n=it.i+(n+1) := by omega
          rw [count]

/-- Complete CURRENT helper Result through the actual Vec iterator ABI. -/
theorem exact (read : CheckpointBytes4Sections.ReadK) (bytes : Slice U8)
    (start : Usize) (v : alloc.vec.Vec K) :
    weights read bytes start v =
      (do let r ← reads read bytes v.val.length start
          match r with
          | .Err e => ok (.Err e)
          | .Ok (xs,last) =>
            let final := write v.deref 0 xs
            ok (.Ok (⟨final.val,final.property⟩,last))) := by
  unfold weights intoIter
  simp only [bind_tc_ok,Aeneas.Std.uncurry]
  change (do let r ← weights_loop read ⟨v.deref,0⟩ (fun im => im) bytes start; finish r)=_
  rw [loop_exact read bytes v.val.length ⟨v.deref,0⟩ (fun im => im) start (by change 0+v.val.length=v.val.length; omega)]

theorem write_shape (pre old xs : List K)
    (bound : (pre++old).length≤Usize.max) (size : xs.length=old.length) :
    (write ⟨pre++old,bound⟩ pre.length xs).val=pre++xs := by
  induction old generalizing pre xs with
  | nil =>
    have empty : xs=[] := List.length_eq_zero_iff.mp size
    subst xs
    rfl
  | cons y old ih =>
    cases xs with
    | nil => simp at size
    | cons x xs =>
      have tailSize : xs.length=old.length := by simpa using size
      have bound1 : ((pre++[y])++old).length≤Usize.max := by
        simpa only [List.append_assoc,List.singleton_append] using bound
      have recursive := ih (pre++[y]) xs bound1 tailSize
      have bound2 : (pre++y::xs).length≤Usize.max := by
        simpa only [List.length_append,List.length_cons,tailSize] using bound
      have same : write ⟨pre++y::old,bound⟩ (pre.length+1) xs=⟨pre++y::xs,bound2⟩ := by
        apply Subtype.ext
        simpa only [List.append_assoc,List.singleton_append,List.length_append,List.length_singleton] using recursive
      simp only [write,same]
      have replaced := CheckpointBytes4Weights.replace_slot pre xs [] y x (by simpa using bound2)
      simpa only [List.append_nil,List.append_assoc,List.singleton_append] using congrArg Subtype.val replaced

#print axioms loop_exact
#print axioms exact
#print axioms write_shape
end AspisR1.Port5Q2_ReaderWeights
end
'''
(L/'Port5Q2_ReaderWeights.lean').write_text(out);(E/'weights-emission.json').write_text(json.dumps({'source_sha256':hashlib.sha256(s.encode()).hexdigest(),'span_start':a,'span_end':b,'span_sha256':hashlib.sha256(s[a:b].encode()).hexdigest(),'module_sha256':hashlib.sha256(out.encode()).hexdigest(),'changes':['namespace/carriers reused from AspisR1Stage2','Reader.k is explicit ReadK','Vec into_iter/back uses explicit TrustedStd content interpretation'],'external_template_imported':False},indent=2)+'\n')
