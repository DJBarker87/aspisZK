from pathlib import Path
R=Path(__file__).resolve().parents[2];p=R/'docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RunJoin_BuildAlpha51.lean'
head='''import R1Z.PV_RunJoin_RoundCanonicalComplete51
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_BuildAlpha51
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46 PV_RunJoin_ResultPost41
open PV_RunJoin_PointPrefix51 (Prefix)
abbrev Q := ProverRwFull.aspis_core.field.QM31

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    {H T1 T2 : Type} (D : aspis_core.digest.Digest32 H)
    (helperInst : core.ops.function.FnOnce T1 (Q × Q) (core.result.Result (alloc.vec.Vec Q) r1_wire.Error))
    (commitInst : host_semantic.Commitments T2)
    (public1 : @aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public (types base))
    (c1 : Array (alloc.vec.Vec aspis_core.field.M31) 26#usize)
    (d g padding : Array Q 1024#usize) (helper : T1) (commitments : T2) (hash : H) (variant : transport.Variant) :
    Post (fun pair => match pair.1 with | .Err _ => True | .Ok built => Prefix 10 built.alpha)
      (@host_semantic.build_with_helper_mode (types base) (selected base heap box ops)
        H T1 T2 D helperInst commitInst public1 c1 d g padding helper commitments hash variant) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  unfold host_semantic.build_with_helper_mode
'''
lines=[];ind=2
simpl='simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,lift,Aeneas.Std.uncurry,bind_assoc_eq]'
def add(s):
 for l in s.splitlines():lines.append(' '*ind+l)
def bind(name):add('apply PV_RunJoin_ResultPost41.bind\nintro '+name)
def status(name,value):
 global ind
 add('cases '+name+' with\n| Err e => trivial\n| Ok '+value+' =>');ind+=2;add('try '+simpl)
def pair(name,parts):bind(name);add('rcases '+name+' with ⟨'+parts+'⟩')
def triple(name,statusName,tr,byte,q):pair(name,','.join([statusName,tr,byte]));status(statusName,q)
def boolean(name):
 global ind
 bind(name);add('cases '+name+' with\n| true => trivial\n| false =>');ind+=2;add('try '+simpl)
bind('checked');status('checked','checkedUnit')
pair('committed','rootStatus,commit1');status('rootStatus','root1')
bind('publicBytes');bind('mappedPublic');status('mappedPublic','pubBytes')
bind('newTranscript');status('newTranscript','t0')
bind('b0');add('try '+simpl)
triple('triple0','status0','t1','b1','lambda')
triple('triple1','status1','t2','b2','chi')
bind('helperResult');status('helperResult','helperValues')
pair('padded','paddingResult,paddedSlice')
bind('mappedPadding');status('mappedPadding','paddingUnit')
add('split\n· trivial\n·');ind+=2
bind('helperSum');bind('zero');boolean('sumDifferent')
pair('committed2','rootStatus2,commit2');status('rootStatus2','root2')
triple('triple2','status2','t3','b3','theta')
triple('zeroRows','zeroStatus','t4','b4','zc')
triple('triple13','status13','t5','b5','mu')
for n in ['columns','dc','maskSum','maskSum1','wide','encoded']:bind(n)
add('try '+simpl)
triple('triple14','status14','t6','b6','eta')
add('apply PV_RunJoin_RecordAppend41.bind_post\n  (PV_RunJoin_RoundCanonicalComplete51.complete base heap box ops D _ _ t6 b6 maskSum1)\nintro sumcheck hcanonical\nrcases sumcheck with ⟨sumcheckStatus,t7,b7⟩')
status('sumcheckStatus','pointRunning');add('rcases pointRunning with ⟨alpha,running⟩')
bind('claimsStatus');status('claimsStatus','claims')
for n in ['stateBefore','alpha8','alpha9','extras','claimBytes']:bind(n)
bind('record25');status('record25','framed25')
pair('circle25','circleStatus25,t8');status('circleStatus25','z0')
for n in ['b8','endpoint']:bind(n)
bind('record26');status('record26','framed26')
pair('circle26','circleStatus26,t9');status('circleStatus26','z1')
bind('b9');boolean('equalPoints');add('exact hcanonical')
s=head+'\n'.join(lines)+'\n#print axioms complete\nend R1Z.PV_RunJoin_BuildAlpha51\n'
import sys
if '--check' in sys.argv:assert p.read_text()==s;print('BuildAlpha51 generator check passed')
else:p.write_text(s)
