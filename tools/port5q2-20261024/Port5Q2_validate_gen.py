from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parents[2];E=R/'evidence/port5q2-20261024';L=R/'docs/research/100bit-spend-path-20261013/lean';s=(E/'reader-helpers/Funs.lean').read_text();a=s.index('def verifier.validate_checkpoint_queries_loop.body');b=s.index('/-- [aspis_r1_cost_probe::verifier::read_checkpoint_weights]',a);body=s[a:b].replace('verifier.validate_checkpoint_queries','validate').replace('18#i32','18#u32')
out='''import Port5Q2_ReaderPrefix
import Port5Q2_Shift
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port5Q2_ReaderValidate
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2
'''+body+'''
theorem contains (s : Slice U32) (q : U32) :
    core.slice.Slice.contains core.cmp.PartialEqU32 s q=ok (decide (q∈s.val)) := by
  unfold core.slice.Slice.contains
  induction s.val with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.anyM,core.cmp.PartialEqU32,lift,bind_tc_ok]
    by_cases same : q=x
    · subst x; simp; rfl
    · simpa [same] using ih

/-- One CURRENT validator iteration reads exactly the physical prefix; the
only shift is the literal18, rebased to the installed Std U32 shift signature. -/
theorem iteration (q : Array U32 22#usize) (i : Usize)
    (pre tail : List U32) (x : U32)
    (shape : q.val=pre++x::tail) (index : i.val=pre.length) :
    validate_loop.body q i = if x.val≥262144 ∨ x∈pre then ok (.done none)
      else ok (.cont (Usize.wrapping_add i 1#usize)) := by
  have room : i.val<q.val.length := by rw [shape,index]; simp
  obtain ⟨value,read,equal⟩ := WP.spec_imp_exists (Array.index_usize_spec q i room)
  have valueEq : value=x := by
    rw [equal]
    simp [shape,index]
  have readX := read.trans (congrArg Result.ok valueEq)
  obtain ⟨front,frontRead,contents⟩ := Port5Q2_ReaderPrefix.read q i (by omega)
  have frontEq : front.val=pre := by rw [contents,shape,index]; simp
  have active : i<Slice.len (Array.to_slice q) := by change i.val<q.val.length; exact room
  simp only [validate_loop.body,lift,bind_tc_ok,if_pos active,readX,
    Port5Q2_Shift.eighteen]
  by_cases high : x.val≥262144
  · simp only [show x≥262144#u32 from high,ite_true,high,true_or]
  · simp only [show ¬x≥262144#u32 from high,ite_false,frontRead,bind_tc_ok]
    rw [contains]
    rw [frontEq]
    by_cases duplicate : x∈pre <;> simp [high,duplicate]

def pending : core.result.Result Unit verifier.Error → Option (core.result.Result Unit verifier.Error)
  | .Ok _ => some (.Ok ())
  | .Err _ => none

/-- Symbolic induction over at most22 actual reads; no concrete query table
or accepted validation is supplied. The same physical prefix is retained. -/
theorem loop_exact (q : Array U32 22#usize) (pre tail : List U32) (i : Usize)
    (shape : q.val=pre++tail) (index : i.val=pre.length) :
    validate_loop q i=ok (pending (CheckpointBytes4Ops.queryLoop pre tail)) := by
  induction tail generalizing pre i with
  | nil =>
    have inactive : ¬ i<Slice.len (Array.to_slice q) := by
      change ¬i.val<q.val.length
      rw [shape,index,List.append_nil]
      omega
    unfold validate_loop
    rw [Aeneas.Std.loop.eq_def]
    simp only [Aeneas.Std.uncurry,validate_loop.body,lift,bind_tc_ok,if_neg inactive,
      CheckpointBytes4Ops.queryLoop,pending]
  | cons x tail ih =>
    have step := iteration q i pre tail x shape index
    unfold validate_loop
    rw [Aeneas.Std.loop.eq_def]
    simp only [Aeneas.Std.uncurry,step]
    by_cases bad : x.val≥262144 ∨ x∈pre
    · simp only [if_pos bad,CheckpointBytes4Ops.queryLoop,pending]
    · simp only [if_neg bad,CheckpointBytes4Ops.queryLoop]
      have small : i.val<22 := by
        have size : q.val.length=22 := q.property
        rw [shape,List.length_append,List.length_cons] at size
        omega
      have next : (Usize.wrapping_add i 1#usize).val=(pre++[x]).length := by
        rw [Port3_Wrapping.increment i (by omega),index,List.length_append,List.length_singleton]
      have shape1 : q.val=(pre++[x])++tail := by
        simpa only [List.append_assoc,List.singleton_append] using shape
      exact ih (pre++[x]) (Usize.wrapping_add i 1#usize) shape1 next

theorem query_result (pre tail : List U32) :
    CheckpointBytes4Ops.queryLoop pre tail=.Ok () ∨
      CheckpointBytes4Ops.queryLoop pre tail=.Err .Checkpoint := by
  induction tail generalizing pre with
  | nil => exact Or.inl rfl
  | cons x tail ih =>
    unfold CheckpointBytes4Ops.queryLoop
    split
    · exact Or.inr rfl
    · exact ih _

/-- COMPLETE current validator Result, including duplicate/out-of-range
rejection, for its actual22-element carrier and installed Std operations. -/
theorem reference (q : Array U32 22#usize) :
    validate q=CheckpointBytes4Ops.validate q := by
  unfold validate CheckpointBytes4Ops.validate
  rw [loop_exact q [] q.val 0#usize rfl rfl,bind_tc_ok]
  rcases query_result [] q.val with good|bad
  · rw [good]; rfl
  · rw [bad]; rfl

#print axioms contains
#print axioms iteration
#print axioms loop_exact
#print axioms query_result
#print axioms reference
end AspisR1.Port5Q2_ReaderValidate
end
'''
(L/'Port5Q2_ReaderValidate.lean').write_text(out);(E/'validate-emission.json').write_text(json.dumps({'source_sha256':hashlib.sha256(s.encode()).hexdigest(),'span_start':a,'span_end':b,'span_sha256':hashlib.sha256(s[a:b].encode()).hexdigest(),'module_sha256':hashlib.sha256(out.encode()).hexdigest(),'changes':['namespace/carriers reused from AspisR1Stage2','literal shift amount18 rebased from emitted I32 to installed Std U32 signature'],'external_template_imported':False},indent=2)+'\n')
