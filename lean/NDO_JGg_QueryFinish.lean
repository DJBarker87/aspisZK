import NDO_JGg_QuerySplit
import NDO_JGg_QueryDecode
set_option autoImplicit false
namespace AspisR1.JGg_QueryFinish
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisR1CurrentCaller.BorrowedClaimPrepared JGg_QuerySplit

theorem source {Hash : Type} (D : aspis_core.Digest32 Hash) (self : transcript.Transcript Hash)
    (b a : Blocks) (q : Array U32 22#usize) (selected : Bytes32)
    (decode : Query31ConcreteMaterializedSchedule.actualConcreteDecode
      Query31ConcreteDriverTraceFacts.sourceDefaultState b a=ok (.Ok (q,selected))) :
    finish closedHashQueries D self b a=ok (.Ok q,{self with state:=selected}) := by
  unfold finish
  change (do
    let r ← Query31ConcreteMaterializedSchedule.actualConcreteDecode
      Query31ConcreteDriverTraceFacts.sourceDefaultState b a
    _) = _
  rw [decode,bind_tc_ok]
  simp only [core.result.Result.map_err,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,Aeneas.Std.uncurry]
  have read0 := JGg_QueryTrace.read q 0#usize (by decide)
  have read1 := JGg_QueryTrace.read q 1#usize (by decide)
  have read2 := JGg_QueryTrace.read q 2#usize (by decide)
  have read3 := JGg_QueryTrace.read q 3#usize (by decide)
  have read4 := JGg_QueryTrace.read q 4#usize (by decide)
  have read5 := JGg_QueryTrace.read q 5#usize (by decide)
  have read6 := JGg_QueryTrace.read q 6#usize (by decide)
  have read7 := JGg_QueryTrace.read q 7#usize (by decide)
  have read8 := JGg_QueryTrace.read q 8#usize (by decide)
  have read9 := JGg_QueryTrace.read q 9#usize (by decide)
  have read10 := JGg_QueryTrace.read q 10#usize (by decide)
  have read11 := JGg_QueryTrace.read q 11#usize (by decide)
  have read12 := JGg_QueryTrace.read q 12#usize (by decide)
  have read13 := JGg_QueryTrace.read q 13#usize (by decide)
  have read14 := JGg_QueryTrace.read q 14#usize (by decide)
  have read15 := JGg_QueryTrace.read q 15#usize (by decide)
  have read16 := JGg_QueryTrace.read q 16#usize (by decide)
  have read17 := JGg_QueryTrace.read q 17#usize (by decide)
  have read18 := JGg_QueryTrace.read q 18#usize (by decide)
  have read19 := JGg_QueryTrace.read q 19#usize (by decide)
  have read20 := JGg_QueryTrace.read q 20#usize (by decide)
  have read21 := JGg_QueryTrace.read q 21#usize (by decide)
  simp only [closedHashQueries,Query31ConcreteMaterializedSchedule.concreteBoundaries]
  simp only [read0,read1,read2,read3,read4,read5,read6,read7,read8,read9,read10,read11,read12,read13,read14,read15,read16,read17,read18,read19,read20,read21,AspisS1M31Embedding.Total.embed_total,bind_tc_ok,trace.value]
#print axioms source
end AspisR1.JGg_QueryFinish
