from pathlib import Path
import sys
def emit(path, text):
 if '--check' in sys.argv: assert path.read_text()==text, path
 else: path.write_text(text)
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
s='''import R1Z.PV_RunJoin_LaneFuns31
import R1Z.PV_RunJoin_OuterABI30
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_LaneABI31
open Aeneas Aeneas.Std Result
namespace N := PV_RunJoin_Lane31
namespace O := PV_RunJoin_Outer30
'''
# Lean does not have namespace aliases; keep fully qualified ABI type names.
s=s[:s.index('namespace N :=')]
N='PV_RunJoin_Lane31.aspis_statement.pool_v1.';O='PV_RunJoin_Outer30.pool_v1.'
np=N+'pair_trace.PoolV1PairInputNoteWitnessV1';op=O+'pair_trace.PoolV1PairInputNoteWitnessV1'
s+=f'''def fromOuter (x : {op}) : {np} :=
  ⟨x.nullifier_key,x.salt,x.value,
    ⟨x.pair_leaf.first_commitment,x.pair_leaf.second_occupied,
      x.pair_leaf.second_commitment,x.pair_leaf.second_occupancy_inverse⟩,
    x.selected_second,⟨x.membership.siblings,x.membership.index⟩⟩

def toOuter (x : {np}) : {op} :=
  ⟨x.nullifier_key,x.salt,x.value,
    ⟨x.pair_leaf.first_commitment,x.pair_leaf.second_occupied,
      x.pair_leaf.second_commitment,x.pair_leaf.second_occupancy_inverse⟩,
    x.selected_second,⟨x.membership.siblings,x.membership.index⟩⟩

theorem roundtrip_outer (x : {op}) : toOuter (fromOuter x) = x := by cases x; rfl
#print axioms roundtrip_outer

theorem roundtrip_lane (x : {np}) : fromOuter (toOuter x) = x := by cases x; rfl
#print axioms roundtrip_lane

'''
ne=N+'pair_tree_profile.PV31_PoolV1PairLeafErrorV1';oe=O+'pair_tree_profile.PV30_PoolV1PairLeafErrorV1'
names=['NonCanonicalCommitment','NonCanonicalOccupancy','NonCanonicalInverse','OccupancyNotBoolean','SentinelInverseMismatch','EmptyInverseNonZero','EmptyCommitmentNonZero','OccupiedSentinelZero','SelectedSlotEmpty']
s+=f'def leafErrorToOuter : {ne} → {oe}\n'+''.join(f'  | .{n} => .{n}\n' for n in names)
s+=f'\ndef leafErrorFromOuter : {oe} → {ne}\n'+''.join(f'  | .{n} => .{n}\n' for n in names)
s+=f'''\ntheorem error_roundtrip (e : {ne}) : leafErrorFromOuter (leafErrorToOuter e) = e := by cases e <;> rfl
#print axioms error_roundtrip
'''
nt=N+'pair_trace.PV31_PoolV1PairTraceErrorV1';ot=O+'pair_trace.PV30_PoolV1PairTraceErrorV1'
trace=['Statement','PairLeaf','Tree','Shape','WrongVariant','RuntimeBinding','NullifierAlreadySpent','WitnessDigest','ValueOutOfRange','Conservation','HashSchedule','SelectedCommitmentMismatch','AnchorMismatch','NullifierMismatch','RecipientCommitmentMismatch','ChangeCommitmentMismatch','SnapshotBindingMismatch','BlockMismatch','AuxiliaryMismatch','MetadataMismatch','CopyLayout','CopyImbalance']
s+=f'\ndef errorToOuter : {nt} → {ot}\n'
for n in trace:
 a={'Statement':1,'PairLeaf':1,'Tree':1,'BlockMismatch':3,'AuxiliaryMismatch':2}.get(n,0);args=['a','b','c'][:a];pat=' '.join(args);rhs='(leafErrorToOuter a)' if n=='PairLeaf' else pat
 s+=f'  | .{n} {pat} => .{n} {rhs}\n'
s+='''
variable [BuilderForestAdmissionPort.ExternalLinear]
def call (x : PV_RunJoin_Outer30.pool_v1.pair_trace.PoolV1PairInputNoteWitnessV1) :
    Result (core.result.Result (Array U32 8#usize)
      PV_RunJoin_Outer30.pool_v1.pair_trace.PV30_PoolV1PairTraceErrorV1) := do
  let r ← PV_RunJoin_Lane31.lane_root (fromOuter x)
  ok (match r with | .Ok d => .Ok d | .Err e => .Err (errorToOuter e))

def native : PV_RunJoin_Outer30.LaneRoot := ⟨call⟩
end R1Z.PV_RunJoin_LaneABI31
'''
# Need the class definition for the native dictionary.
s=s.replace('import R1Z.PV_RunJoin_OuterABI30','import R1Z.PV_RunJoin_OuterExternal30')
emit(L/'PV_RunJoin_LaneABI31.lean',s)
