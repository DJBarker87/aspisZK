from pathlib import Path
import sys
R=Path(__file__).resolve().parents[2];p=R/'docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RunJoin_PreparedCaller32.lean'
s='''import R1Z.PV_RunJoin_CanonicalCoverage31
import R1Z.PV_RunJoin_HonestPremises32
import R1Z.PV_RunJoin_NativeCallerFrame32
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PreparedCaller32
open Aeneas Aeneas.Std Result PV_RunJoin_Outer30 PV_RunJoin_HonestIdentification26
local instance : BuilderForestAdmissionPort.ExternalLinear := PV_RunJoin_ShippedExternal.E_shipped
local instance : BuilderForestAdmissionPort.Records := PV_RunJoin_UniversalRecords22.shipped
local instance : LaneRoot := PV_RunJoin_LaneABI31.native
local instance : ProverRwRngCaller.NativeTypes := PV_RunJoin_CallerWorld.nativeTypes
local instance : ProverRwRngCaller.ErasureFns := ⟨fun _ value => .ok value,fun _ value => .ok value⟩
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]
variable {N C : Type}
variable (base : ProverRwFull.ExternalTypes)
    (ops : PV_RunJoin_NativeSelectedInputs.SourceState base N C →
      @ProverRwFull.ExternalFuns (PDict_CodecDictionary.native base))
    (hash : Slice (Slice U8) → Result (Array U8 32#usize))
'''
for kind,title,fn in [('transfer','PrivateTransfer','private_transfer'),('withdrawal','Withdrawal','withdrawal')]:
 i=f'(PV_RunJoin_OuterChecked30.{kind}Input p w root (PV_RunJoin_CodecOuter30.snapshot snapshot) c)'
 s+=f'''
/-- Every successful canonical preparation supplies the actual caller's full
public and ORIGINAL returned payload, plus its canonical semantic coordinates.
No residual admission/word/record/payload-association premise is assumed. -/
theorem {kind} (bytes : Slice U8)
    (p : pool_v1.payment_relation.PoolV1{title}PublicV1)
    (w : pool_v1.pair_forest_trace.PoolV1PairForest{title}WitnessV1)
    (context : pool_v1.payment_relation.PoolV1PaymentRelationContextV1)
    (snapshot : PV_RunJoin_CodecOuter30.Snapshot)
    (c : pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (h : PV_RunJoin_CodecOuter30.run bytes
      (pool_v1.pair_forest_trace.compile_pool_v1_pair_forest_{fn}_merged_c1_v1 p w context) = ok (.Ok (snapshot,c))) :
    ∃ root, pool_v1.pair_forest_trace.lane_root w.input.pair = ok (.Ok root) ∧
      ∃ hi : PV_RunJoin_ConsumerBoundary25.HonestInput (K := K) {i},
      let i : Honest (K := K) := ⟨{i},hi⟩
      ∀ state : PV_RunJoin_NativeSelectedInputs.SourceState base N C,
      letI : ProverRwFull.ExternalTypes := PDict_CodecDictionary.native base
      PV_RunJoin_NativePublicInverse32.unPublic base
        ((PV_RunJoin_NativeSelectedInputs.inputs base ops hash i.val).pub state) =
          PV_Src_NativeInput.publicInput i.val ∧
      PV_RunJoin_OuterABI30.compilationFromForest
        (PV_RunJoin_NominalCompiledData.unCompiled base
          ((PV_RunJoin_NativeSelectedInputs.inputs base ops hash i.val).compiled state)) = c ∧
      PV_RunJoin_SelectedCoordinates32.semantic base
        ((PV_RunJoin_NativeSelectedInputs.inputs base ops hash i.val).pub state) =
          BuilderSource.prover.public (target i) ∧
      PV_Src_NativeInput.columns PV_Src_Forest_Columns.read
        ((PV_RunJoin_NativeSelectedInputs.inputs base ops hash i.val).compiled state).semantic_c1.c1 =
          BuilderSource.prover.build (target i) := by
  obtain ⟨root,hr,hi⟩ := PV_RunJoin_CanonicalHonest31.{kind} (K := K) bytes p w context snapshot c h
  refine ⟨root,hr,hi,?_⟩
  let i : Honest (K := K) := ⟨{i},hi⟩
  dsimp only
  intro state
  letI : ProverRwFull.ExternalTypes := PDict_CodecDictionary.native base
  refine ⟨PV_RunJoin_NativeCallerFrame32.complete_public base ops hash i.val state,?_,
    PV_RunJoin_SelectedCoordinates32.caller_public base ops hash i state,
    PV_RunJoin_SelectedCoordinates32.caller_columns base ops hash i state⟩
  rw [PV_RunJoin_NativeCallerFrame32.complete_compiled]
  exact PV_RunJoin_OuterABILaws30.compilation_reverse c
#print axioms {kind}
'''
s+='end R1Z.PV_RunJoin_PreparedCaller32\n'
if '--check' in sys.argv:assert p.read_text()==s
else:p.write_text(s)
print('prepared-caller symbolic generator check' if '--check' in sys.argv else 'wrote prepared-caller source')
