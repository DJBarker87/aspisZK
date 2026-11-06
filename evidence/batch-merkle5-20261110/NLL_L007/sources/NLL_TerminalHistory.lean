import NLL_State
set_option autoImplicit false
noncomputable section
namespace NLL_TerminalHistory
open Aeneas Aeneas.Std Result AspisR1 MultiproofConeRef NLL
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
attribute [local instance] Classical.propDecidable

theorem source (H : Bytes → State) (root : NLL.Root) (batch : Nat) (kind : Usize)
 (nodes : Slice U8) (s : reference.Scratch)
 (width : nodes.val.length=32*OraclePortSelectedDraft.capacity (3*batch+kind.val))
 (bytes : (MultiproofConeSlotTail.prefixNodes nodes (OraclePortFrozenOrder.nodeCount 18 (NJV_UnitDomain.keys s))).val.length≤9216)
 (events : List Event) (out : NLL.Answer) (native : Terminal H root batch kind.val nodes s events out) :
 leafHistory kind events=NKV_QueryPlan.tail H batch kind.val nodes root s := by
 cases native with
 | missing bad => simp only [NKV_QueryPlan.tail,if_neg bad,leafHistory,List.flatMap_cons,List.flatMap_nil,List.nil_append]
 | capacity well excess =>
   have no : ¬(OraclePortFrozenOrder.nodeCount 18 (NJV_UnitDomain.keys s)≤OraclePortSelectedDraft.capacity (3*batch+kind.val) ∧
       MultiproofConePadding.scan _ _=true) := by intro h;omega
   simp only [NKV_QueryPlan.tail,if_pos well,if_neg no,leafHistory,List.flatMap_cons,List.flatMap_nil,List.nil_append]
 | padding well fits bad =>
   simp only [NKV_QueryPlan.tail,if_pos well,bad,Bool.false_eq_true,and_false,if_false,
     leafHistory,List.flatMap_cons,List.flatMap_nil,List.nil_append]
 | verify well fits pad queries answer child =>
   have packet:=NKV_VerifyInvocation.returning H root _ s.idx s.val s.n bytes queries answer child
   have logs:=congrArg Prod.fst packet
   simp only [NKV_QueryPlan.tail,if_pos well,fits,pad,and_self,if_true,
     leafHistory,List.flatMap_cons,List.flatMap_nil,List.append_nil]
   exact logs.symm

set_option pp.proofs false
#print source
#print axioms source
end NLL_TerminalHistory
end
