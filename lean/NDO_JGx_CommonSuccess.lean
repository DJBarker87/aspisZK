import RPz7_Tx2I_Cuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGx_CommonSuccess
open Aeneas Aeneas.Std Result VTop_Stages

theorem source (ops : Ops) {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (pub proof cp : Slice U8) (p : verifier.Prepared) (a out : verifier.Accumulator)
    (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (inactive : aspis_core.field.wide_exact.WideExact) (ir fr : Slice U8)
    (folded : Array U8 32#usize) (geo : verifier.QueryGeometry) (pending after : verifier.BatchedWeights)
    (read : ops.op18 D cp proof pub .S2 hash=ok (.Ok (p,a)))
    (next : a.next=10#usize) (split : ops.op16=ok 10#usize)
    (powers : ops.op17 29#usize p.gamma=ok g)
    (mark : ∀ phase,ops.op13 none phase=ok ())
    (off0 : ops.op23=ok 7495#usize) (off1 : ops.op22=ok 7527#usize)
    (readInactive : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      proof {start:=7495#usize,«end»:=7527#usize}=ok ir)
    (decode : ops.op2 ir=ok (some inactive))
    (option : ops.op0 (some inactive) AdapterRw.aspis_r1_cost_probe.verifier.Error.Parse=ok (.Ok inactive))
    (off2 : ops.op15=ok 7751#usize) (off3 : ops.op14=ok 7783#usize)
    (readFolded : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      proof {start:=7751#usize,«end»:=7783#usize}=ok fr)
    (array : core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 fr=ok (.Ok folded))
    (unwrap : ops.unwrap32 (.Ok folded)=ok folded)
    (batch : ops.op5 D proof p folded 1#usize hash=ok (.Ok ()))
    (geometry : ops.op11 p.queries 10#usize 22#usize=ok (.Ok geo))
    (newPending : ops.op10 a.weights.deref=ok (.Ok pending))
    (query : ops.op6 proof p a g none geo pending 22#usize=ok (.Ok (out,after)))
    (tail : Tx2I_Cuts.tail ops proof p none inactive 7527#usize 7751#usize 7783#usize
      (out,after)=ok (.Ok ())) :
    verifier.candidate.tx2_common ops D pub proof cp hash none=ok (.Ok ()) := by
  rw [←Tx2I_Cuts.common_source]
  unfold Tx2I_Cuts.common
  rw [read,bind_tc_ok]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,Aeneas.Std.uncurry]
  rw [split,bind_tc_ok,next]
  simp only [show (10#usize !=10#usize)=false from by decide,Bool.false_eq_true,ite_false]
  rw [powers,bind_tc_ok,mark,bind_tc_ok,off0,bind_tc_ok,off1,bind_tc_ok,
    readInactive,bind_tc_ok,decode,bind_tc_ok,option,bind_tc_ok]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  rw [off2,bind_tc_ok,off3,bind_tc_ok,readFolded,bind_tc_ok,array,bind_tc_ok,unwrap,bind_tc_ok,
    batch,bind_tc_ok]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  rw [mark,bind_tc_ok,geometry,bind_tc_ok]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  rw [newPending,bind_tc_ok]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  rw [query,bind_tc_ok]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  exact tail
#print axioms source
end AspisR1.JGx_CommonSuccess
end
