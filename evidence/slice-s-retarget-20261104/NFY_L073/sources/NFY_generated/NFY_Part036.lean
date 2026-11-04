import Lean
import NFY_Part022
import NFY_Part035
import NFY_Part020
import NFY_Part023
import NFY_Part034

-- BEGIN copied JFt_Digest37: lean/JFt_Digest37.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFt_Digest37
open Aeneas Aeneas.Std Result

def value : Array AspisR1TerminalDecoder.aspis_core.field.M31 8#usize :=
  Array.make 8#usize [1239966481#u32,992485427#u32,1397515674#u32,466658549#u32,2071909237#u32,712995354#u32,2047452742#u32,1680224983#u32]

/-- Exact numeric value is identified by the symbolic byte-injectivity lemma. -/
theorem local_call : AspisS6NativeSnapshotReadDigest.read_digest NFY_JFu_PublicDigest37.window=ok (.Ok value) := by
  obtain ⟨out,call,canon,contents⟩:=NFY_JFu_DigestSliceFacts.source NFY_JFu_PublicDigest37.window
    NFY_JFu_PublicDigest37.length NFY_JFu_PublicDigest37.canonical_bytes
  have bytes : AspisS6SourceCodec.DigestContents.chunks value=NFY_JFu_PublicDigest37.bytes := by
    simp [AspisS6SourceCodec.DigestContents.chunks,value,Array.make,core.num.U32.to_le_bytes,BitVec.toLEBytes,NFY_JFu_PublicDigest37.bytes]
    <;> (repeat' constructor) <;> scalar_tac
  have same : out=value := NFY_JFt_DigestInjective.injective out value (contents.trans bytes.symm)
  rw [same] at call
  exact call

theorem selected : NFY_JFu_PublicRange.segment 1472 32 (by decide)=NFY_JFu_PublicDigest37.window := by
  apply Subtype.ext
  dsimp only [NFY_JFu_PublicRange.segment,NFY_JFu_PublicDigest37.window]
  exact NFY_JFu_PublicDigest37.selected

theorem source : AspisS6NativeSnapshotReadDigest.read_digest
    (NFY_JFu_PublicRange.segment 1472 32 (by decide))=ok (.Ok value) := by
  rw [selected]
  exact local_call

theorem canonical : NFY_JFu_DigestCanonical.Canonical value :=
  NFY_JFu_DigestSliceCanonical.source _ _ source

#print axioms local_call
#print axioms selected
#print axioms source
#print axioms canonical
end AspisR1.NFY_JFt_Digest37
-- END copied JFt_Digest37
-- BEGIN copied JFt_Digest38: lean/JFt_Digest38.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFt_Digest38
open Aeneas Aeneas.Std Result

def value : Array AspisR1TerminalDecoder.aspis_core.field.M31 8#usize :=
  Array.make 8#usize [1796237568#u32,1862343136#u32,1954463912#u32,1190686266#u32,364700025#u32,46960257#u32,671215600#u32,1214723477#u32]

/-- Exact numeric value is identified by the symbolic byte-injectivity lemma. -/
theorem local_call : AspisS6NativeSnapshotReadDigest.read_digest NFY_JFu_PublicDigest38.window=ok (.Ok value) := by
  obtain ⟨out,call,canon,contents⟩:=NFY_JFu_DigestSliceFacts.source NFY_JFu_PublicDigest38.window
    NFY_JFu_PublicDigest38.length NFY_JFu_PublicDigest38.canonical_bytes
  have bytes : AspisS6SourceCodec.DigestContents.chunks value=NFY_JFu_PublicDigest38.bytes := by
    simp [AspisS6SourceCodec.DigestContents.chunks,value,Array.make,core.num.U32.to_le_bytes,BitVec.toLEBytes,NFY_JFu_PublicDigest38.bytes]
    <;> (repeat' constructor) <;> scalar_tac
  have same : out=value := NFY_JFt_DigestInjective.injective out value (contents.trans bytes.symm)
  rw [same] at call
  exact call

theorem selected : NFY_JFu_PublicRange.segment 1504 32 (by decide)=NFY_JFu_PublicDigest38.window := by
  apply Subtype.ext
  dsimp only [NFY_JFu_PublicRange.segment,NFY_JFu_PublicDigest38.window]
  exact NFY_JFu_PublicDigest38.selected

theorem source : AspisS6NativeSnapshotReadDigest.read_digest
    (NFY_JFu_PublicRange.segment 1504 32 (by decide))=ok (.Ok value) := by
  rw [selected]
  exact local_call

theorem canonical : NFY_JFu_DigestCanonical.Canonical value :=
  NFY_JFu_DigestSliceCanonical.source _ _ source

#print axioms local_call
#print axioms selected
#print axioms source
#print axioms canonical
end AspisR1.NFY_JFt_Digest38
-- END copied JFt_Digest38
-- BEGIN copied JFt_Digest39: lean/JFt_Digest39.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFt_Digest39
open Aeneas Aeneas.Std Result

def value : Array AspisR1TerminalDecoder.aspis_core.field.M31 8#usize :=
  Array.make 8#usize [1127845264#u32,662862400#u32,84021756#u32,995080286#u32,1419670571#u32,1966281459#u32,837284626#u32,2083375353#u32]

/-- Exact numeric value is identified by the symbolic byte-injectivity lemma. -/
theorem local_call : AspisS6NativeSnapshotReadDigest.read_digest NFY_JFu_PublicDigest39.window=ok (.Ok value) := by
  obtain ⟨out,call,canon,contents⟩:=NFY_JFu_DigestSliceFacts.source NFY_JFu_PublicDigest39.window
    NFY_JFu_PublicDigest39.length NFY_JFu_PublicDigest39.canonical_bytes
  have bytes : AspisS6SourceCodec.DigestContents.chunks value=NFY_JFu_PublicDigest39.bytes := by
    simp [AspisS6SourceCodec.DigestContents.chunks,value,Array.make,core.num.U32.to_le_bytes,BitVec.toLEBytes,NFY_JFu_PublicDigest39.bytes]
    <;> (repeat' constructor) <;> scalar_tac
  have same : out=value := NFY_JFt_DigestInjective.injective out value (contents.trans bytes.symm)
  rw [same] at call
  exact call

theorem selected : NFY_JFu_PublicRange.segment 1536 32 (by decide)=NFY_JFu_PublicDigest39.window := by
  apply Subtype.ext
  dsimp only [NFY_JFu_PublicRange.segment,NFY_JFu_PublicDigest39.window]
  exact NFY_JFu_PublicDigest39.selected

theorem source : AspisS6NativeSnapshotReadDigest.read_digest
    (NFY_JFu_PublicRange.segment 1536 32 (by decide))=ok (.Ok value) := by
  rw [selected]
  exact local_call

theorem canonical : NFY_JFu_DigestCanonical.Canonical value :=
  NFY_JFu_DigestSliceCanonical.source _ _ source

#print axioms local_call
#print axioms selected
#print axioms source
#print axioms canonical
end AspisR1.NFY_JFt_Digest39
-- END copied JFt_Digest39
-- BEGIN copied JFt_Digest40: lean/JFt_Digest40.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFt_Digest40
open Aeneas Aeneas.Std Result

def value : Array AspisR1TerminalDecoder.aspis_core.field.M31 8#usize :=
  Array.make 8#usize [1321679286#u32,782621548#u32,1415820264#u32,74436574#u32,776350425#u32,323154748#u32,429051705#u32,1299980413#u32]

/-- Exact numeric value is identified by the symbolic byte-injectivity lemma. -/
theorem local_call : AspisS6NativeSnapshotReadDigest.read_digest NFY_JFu_PublicDigest40.window=ok (.Ok value) := by
  obtain ⟨out,call,canon,contents⟩:=NFY_JFu_DigestSliceFacts.source NFY_JFu_PublicDigest40.window
    NFY_JFu_PublicDigest40.length NFY_JFu_PublicDigest40.canonical_bytes
  have bytes : AspisS6SourceCodec.DigestContents.chunks value=NFY_JFu_PublicDigest40.bytes := by
    simp [AspisS6SourceCodec.DigestContents.chunks,value,Array.make,core.num.U32.to_le_bytes,BitVec.toLEBytes,NFY_JFu_PublicDigest40.bytes]
    <;> (repeat' constructor) <;> scalar_tac
  have same : out=value := NFY_JFt_DigestInjective.injective out value (contents.trans bytes.symm)
  rw [same] at call
  exact call

theorem selected : NFY_JFu_PublicRange.segment 1568 32 (by decide)=NFY_JFu_PublicDigest40.window := by
  apply Subtype.ext
  dsimp only [NFY_JFu_PublicRange.segment,NFY_JFu_PublicDigest40.window]
  exact NFY_JFu_PublicDigest40.selected

theorem source : AspisS6NativeSnapshotReadDigest.read_digest
    (NFY_JFu_PublicRange.segment 1568 32 (by decide))=ok (.Ok value) := by
  rw [selected]
  exact local_call

theorem canonical : NFY_JFu_DigestCanonical.Canonical value :=
  NFY_JFu_DigestSliceCanonical.source _ _ source

#print axioms local_call
#print axioms selected
#print axioms source
#print axioms canonical
end AspisR1.NFY_JFt_Digest40
-- END copied JFt_Digest40
-- BEGIN copied JFt_Digest41: lean/JFt_Digest41.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFt_Digest41
open Aeneas Aeneas.Std Result

def value : Array AspisR1TerminalDecoder.aspis_core.field.M31 8#usize :=
  Array.make 8#usize [1519171444#u32,1235587172#u32,1671492368#u32,1449613582#u32,547369941#u32,1621086153#u32,266860322#u32,450526803#u32]

/-- Exact numeric value is identified by the symbolic byte-injectivity lemma. -/
theorem local_call : AspisS6NativeSnapshotReadDigest.read_digest NFY_JFu_PublicDigest41.window=ok (.Ok value) := by
  obtain ⟨out,call,canon,contents⟩:=NFY_JFu_DigestSliceFacts.source NFY_JFu_PublicDigest41.window
    NFY_JFu_PublicDigest41.length NFY_JFu_PublicDigest41.canonical_bytes
  have bytes : AspisS6SourceCodec.DigestContents.chunks value=NFY_JFu_PublicDigest41.bytes := by
    simp [AspisS6SourceCodec.DigestContents.chunks,value,Array.make,core.num.U32.to_le_bytes,BitVec.toLEBytes,NFY_JFu_PublicDigest41.bytes]
    <;> (repeat' constructor) <;> scalar_tac
  have same : out=value := NFY_JFt_DigestInjective.injective out value (contents.trans bytes.symm)
  rw [same] at call
  exact call

theorem selected : NFY_JFu_PublicRange.segment 1600 32 (by decide)=NFY_JFu_PublicDigest41.window := by
  apply Subtype.ext
  dsimp only [NFY_JFu_PublicRange.segment,NFY_JFu_PublicDigest41.window]
  exact NFY_JFu_PublicDigest41.selected

theorem source : AspisS6NativeSnapshotReadDigest.read_digest
    (NFY_JFu_PublicRange.segment 1600 32 (by decide))=ok (.Ok value) := by
  rw [selected]
  exact local_call

theorem canonical : NFY_JFu_DigestCanonical.Canonical value :=
  NFY_JFu_DigestSliceCanonical.source _ _ source

#print axioms local_call
#print axioms selected
#print axioms source
#print axioms canonical
end AspisR1.NFY_JFt_Digest41
-- END copied JFt_Digest41
-- BEGIN copied JFt_Digest42: lean/JFt_Digest42.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFt_Digest42
open Aeneas Aeneas.Std Result

def value : Array AspisR1TerminalDecoder.aspis_core.field.M31 8#usize :=
  Array.make 8#usize [19381883#u32,1308966873#u32,251977766#u32,474343397#u32,2069732268#u32,1863820229#u32,152153379#u32,665567443#u32]

/-- Exact numeric value is identified by the symbolic byte-injectivity lemma. -/
theorem local_call : AspisS6NativeSnapshotReadDigest.read_digest NFY_JFu_PublicDigest42.window=ok (.Ok value) := by
  obtain ⟨out,call,canon,contents⟩:=NFY_JFu_DigestSliceFacts.source NFY_JFu_PublicDigest42.window
    NFY_JFu_PublicDigest42.length NFY_JFu_PublicDigest42.canonical_bytes
  have bytes : AspisS6SourceCodec.DigestContents.chunks value=NFY_JFu_PublicDigest42.bytes := by
    simp [AspisS6SourceCodec.DigestContents.chunks,value,Array.make,core.num.U32.to_le_bytes,BitVec.toLEBytes,NFY_JFu_PublicDigest42.bytes]
    <;> (repeat' constructor) <;> scalar_tac
  have same : out=value := NFY_JFt_DigestInjective.injective out value (contents.trans bytes.symm)
  rw [same] at call
  exact call

theorem selected : NFY_JFu_PublicRange.segment 1632 32 (by decide)=NFY_JFu_PublicDigest42.window := by
  apply Subtype.ext
  dsimp only [NFY_JFu_PublicRange.segment,NFY_JFu_PublicDigest42.window]
  exact NFY_JFu_PublicDigest42.selected

theorem source : AspisS6NativeSnapshotReadDigest.read_digest
    (NFY_JFu_PublicRange.segment 1632 32 (by decide))=ok (.Ok value) := by
  rw [selected]
  exact local_call

theorem canonical : NFY_JFu_DigestCanonical.Canonical value :=
  NFY_JFu_DigestSliceCanonical.source _ _ source

#print axioms local_call
#print axioms selected
#print axioms source
#print axioms canonical
end AspisR1.NFY_JFt_Digest42
-- END copied JFt_Digest42
-- BEGIN copied JFu_DigestCheck: lean/JFu_DigestCheck.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFu_DigestCheck
open Aeneas Aeneas.Std Result WP
open AspisR1TerminalDecoder

theorem source (digest : Array U32 8#usize) (canon : NFY_JFu_DigestCanonical.Canonical digest) :
    pool_v1.pair_tree_profile.digest_is_canonical digest=ok true := by
  have spec : pool_v1.pair_tree_profile.digest_is_canonical digest ⦃ b => b=true ⦄ := by
    unfold pool_v1.pair_tree_profile.digest_is_canonical
      pool_v1.pair_tree_profile.digest_is_canonical_loop
    refine loop.spec_decr_nat
      (fun i : Usize => 8-i.val) (fun i : Usize => i.val≤8)
      (fun b : Bool => b=true)
      (fun i => pool_v1.pair_tree_profile.digest_is_canonical_loop.body digest i) 0#usize ?_ ?_
    · intro i hi
      unfold pool_v1.pair_tree_profile.digest_is_canonical_loop.body
      step*
      all_goals first
        | scalar_tac
        | (have hc:=canon ⟨i.val,by scalar_tac⟩
           unfold aspis_core.field.P at *
           simp_all [NFY_JFu_DigestCanonical.Canonical]
           scalar_tac)
    · scalar_tac
  obtain ⟨b,call,same⟩:=WP.spec_imp_exists spec
  rw [same] at call
  exact call

@[local step] theorem step (digest : Array U32 8#usize) (canon : NFY_JFu_DigestCanonical.Canonical digest) :
    pool_v1.pair_tree_profile.digest_is_canonical digest ⦃ b => b=true ⦄ := by
  rw [source digest canon,WP.spec_ok]

#print axioms source
#print axioms step
end AspisR1.NFY_JFu_DigestCheck
-- END copied JFu_DigestCheck
-- BEGIN copied JFu_AfterstateFrontier: lean/JFu_AfterstateFrontier.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFu_AfterstateFrontier
open Aeneas Aeneas.Std Result WP
open AspisR1TerminalDecoder

@[local step] theorem digest (q : Array U32 8#usize) (canon : NFY_JFu_DigestCanonical.Canonical q) :
    pool_v1.pair_tree_profile.digest_is_canonical q ⦃ b => b=true ⦄ := by
  rw [NFY_JFu_DigestCheck.source q canon,WP.spec_ok]

theorem source (a : Array (Array U32 8#usize) 20#usize)
    (canon : ∀ i : Fin 20,NFY_JFu_DigestCanonical.Canonical
      (a.val[i.val]'(by simpa only [a.property,show (20#usize).val=20 from rfl] using i.isLt))) :
    pool_v1.pair_terminal.validate_verified_afterstate_loop a 0#usize=ok (.Ok ()) := by
  have spec : pool_v1.pair_terminal.validate_verified_afterstate_loop a 0#usize
      ⦃ out => out=.Ok () ⦄ := by
    unfold pool_v1.pair_terminal.validate_verified_afterstate_loop
    refine loop.spec_decr_nat
      (fun i : Usize => 20-i.val) (fun i : Usize => i.val≤20)
      (fun out => out=.Ok ())
      (fun i => pool_v1.pair_terminal.validate_verified_afterstate_loop.body a i)
      0#usize ?_ ?_
    · intro i hi
      unfold pool_v1.pair_terminal.validate_verified_afterstate_loop.body
      step*
      all_goals first
        | scalar_tac
        | (simp_all;exact canon ⟨i.val,by scalar_tac⟩)
    · scalar_tac
  obtain ⟨out,call,same⟩:=WP.spec_imp_exists spec
  rw [same] at call
  exact call

#print axioms digest
#print axioms source
end AspisR1.NFY_JFu_AfterstateFrontier
-- END copied JFu_AfterstateFrontier
-- BEGIN copied JFu_FrontierCheck: lean/JFu_FrontierCheck.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFu_FrontierCheck
open Aeneas Aeneas.Std Result WP
open AspisR1TerminalDecoder

@[local step] theorem digest (q : Array U32 8#usize) (canon : NFY_JFu_DigestCanonical.Canonical q) :
    pool_v1.pair_tree_profile.digest_is_canonical q ⦃ b => b=true ⦄ := by
  rw [NFY_JFu_DigestCheck.source q canon,WP.spec_ok]

theorem source (a : Array (Array U32 8#usize) 20#usize)
    (canon : ∀ i : Fin 20,NFY_JFu_DigestCanonical.Canonical
      (a.val[i.val]'(by simpa only [a.property,show (20#usize).val=20 from rfl] using i.isLt))) :
    pool_v1.pair_tree_profile.validate_pool_v1_pair_live_snapshot_v1_loop a 0#usize=ok (.Ok ()) := by
  have spec : pool_v1.pair_tree_profile.validate_pool_v1_pair_live_snapshot_v1_loop a 0#usize
      ⦃ out => out=.Ok () ⦄ := by
    unfold pool_v1.pair_tree_profile.validate_pool_v1_pair_live_snapshot_v1_loop
    refine loop.spec_decr_nat
      (fun i : Usize => 20-i.val) (fun i : Usize => i.val≤20)
      (fun out => out=.Ok ())
      (fun i => pool_v1.pair_tree_profile.validate_pool_v1_pair_live_snapshot_v1_loop.body a i)
      0#usize ?_ ?_
    · intro i hi
      unfold pool_v1.pair_tree_profile.validate_pool_v1_pair_live_snapshot_v1_loop.body
      step*
      all_goals first
        | scalar_tac
        | (simp_all;exact canon ⟨i.val,by scalar_tac⟩)
    · scalar_tac
  obtain ⟨out,call,same⟩:=WP.spec_imp_exists spec
  rw [same] at call
  exact call

#print axioms digest
#print axioms source
end AspisR1.NFY_JFu_FrontierCheck
-- END copied JFu_FrontierCheck
-- BEGIN copied JFu_SnapshotValidator: lean/JFu_SnapshotValidator.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFu_SnapshotValidator
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder
open pool_v1.pair_tree_profile

theorem capacity : POOL_V1_PAIR_CAPACITY=ok 1048576#u64 := by
  unfold POOL_V1_PAIR_CAPACITY POOL_V1_PAIR_TREE_DEPTH pool_v1.format.POOL_V1_TREE_DEPTH
  rfl

theorem source (s : PoolV1PairLiveSnapshotV1)
    (pool : core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 s.pool (Array.repeat 32#usize 0#u8)=ok false)
    (domain : core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 s.deployment_domain (Array.repeat 32#usize 0#u8)=ok false)
    (sequence : s.sequence=s.next_pair_index) (small : s.next_pair_index.val<1048576)
    (root : NFY_JFu_DigestCanonical.Canonical s.current_root)
    (frontier : ∀ i : Fin 20,NFY_JFu_DigestCanonical.Canonical
      (s.frontier.val[i.val]'(by simpa only [s.frontier.property,show (20#usize).val=20 from rfl] using i.isLt))) :
    validate_pool_v1_pair_live_snapshot_v1 s=ok (.Ok ()) := by
  unfold validate_pool_v1_pair_live_snapshot_v1
  dsimp only
  rw [pool,bind_tc_ok]
  simp only [Bool.false_eq_true,↓reduceIte]
  rw [domain,bind_tc_ok]
  simp only [Bool.false_eq_true,↓reduceIte]
  have check : ¬s.next_pair_index ≥ 1048576#u64 := by scalar_tac
  have seqCheck : (s.sequence != s.next_pair_index)=false := by simp [sequence]
  simp only [seqCheck,Bool.false_eq_true,↓reduceIte,capacity,bind_tc_ok,if_neg check]
  rw [NFY_JFu_DigestCheck.source s.current_root root,bind_tc_ok]
  simp only [↓reduceIte]
  exact NFY_JFu_FrontierCheck.source s.frontier frontier

#print axioms capacity
#print axioms source
end AspisR1.NFY_JFu_SnapshotValidator
-- END copied JFu_SnapshotValidator
-- BEGIN copied JFu_AfterstateValidator: lean/JFu_AfterstateValidator.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFu_AfterstateValidator
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder
open pool_v1.pair_terminal

theorem source (s : PoolV1PairVerifiedAfterstateV1)
    (positive : s.next_pair_index.val>0) (small : s.next_pair_index.val≤1048576)
    (root : NFY_JFu_DigestCanonical.Canonical s.next_root)
    (frontier : ∀ i : Fin 20,NFY_JFu_DigestCanonical.Canonical
      (s.next_frontier.val[i.val]'(by simpa only [s.next_frontier.property,show (20#usize).val=20 from rfl] using i.isLt))) :
    validate_verified_afterstate s=ok (.Ok ()) := by
  unfold validate_verified_afterstate
  have nonzero : s.next_pair_index≠0#u64 := by scalar_tac
  have bounded : ¬s.next_pair_index>1048576#u64 := by scalar_tac
  simp only [if_neg nonzero,NFY_JFu_SnapshotValidator.capacity,bind_tc_ok,if_neg bounded]
  rw [NFY_JFu_DigestCheck.source s.next_root root,bind_tc_ok]
  simp only [↓reduceIte]
  exact NFY_JFu_AfterstateFrontier.source s.next_frontier frontier

#print axioms source
end AspisR1.NFY_JFu_AfterstateValidator
-- END copied JFu_AfterstateValidator
-- BEGIN copied JFt_AfterstateValue: lean/JFt_AfterstateValue.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFt_AfterstateValue
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder pool_v1.pair_terminal

def value : PoolV1PairVerifiedAfterstateV1 :=
  {next_pair_index:=14#u64,next_root:=NFY_JFt_Digest22.value,
   next_frontier:=Array.make 20#usize [NFY_JFt_Digest23.value,NFY_JFt_Digest24.value,NFY_JFt_Digest25.value,NFY_JFt_Digest26.value,NFY_JFt_Digest27.value,NFY_JFt_Digest28.value,NFY_JFt_Digest29.value,NFY_JFt_Digest30.value,NFY_JFt_Digest31.value,NFY_JFt_Digest32.value,NFY_JFt_Digest33.value,NFY_JFt_Digest34.value,NFY_JFt_Digest35.value,NFY_JFt_Digest36.value,NFY_JFt_Digest37.value,NFY_JFt_Digest38.value,NFY_JFt_Digest39.value,NFY_JFt_Digest40.value,NFY_JFt_Digest41.value,NFY_JFt_Digest42.value]}

theorem frontier : ∀ i : Fin 20,NFY_JFu_DigestCanonical.Canonical
    (value.next_frontier.val[i.val]'(by simp only [value,Array.make];exact i.isLt)) := by
  intro i
  fin_cases i
  · exact NFY_JFt_Digest23.canonical
  · exact NFY_JFt_Digest24.canonical
  · exact NFY_JFt_Digest25.canonical
  · exact NFY_JFt_Digest26.canonical
  · exact NFY_JFt_Digest27.canonical
  · exact NFY_JFt_Digest28.canonical
  · exact NFY_JFt_Digest29.canonical
  · exact NFY_JFt_Digest30.canonical
  · exact NFY_JFt_Digest31.canonical
  · exact NFY_JFt_Digest32.canonical
  · exact NFY_JFt_Digest33.canonical
  · exact NFY_JFt_Digest34.canonical
  · exact NFY_JFt_Digest35.canonical
  · exact NFY_JFt_Digest36.canonical
  · exact NFY_JFt_Digest37.canonical
  · exact NFY_JFt_Digest38.canonical
  · exact NFY_JFt_Digest39.canonical
  · exact NFY_JFt_Digest40.canonical
  · exact NFY_JFt_Digest41.canonical
  · exact NFY_JFt_Digest42.canonical

theorem validated : validate_verified_afterstate value=ok (.Ok ()) :=
  NFY_JFu_AfterstateValidator.source value (by decide) (by decide) NFY_JFt_Digest22.canonical frontier

#print axioms frontier
#print axioms validated
end AspisR1.NFY_JFt_AfterstateValue
-- END copied JFt_AfterstateValue
-- BEGIN copied JFu_PublicMeta02: lean/JFu_PublicMeta02.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFu_PublicMeta02
open Aeneas Aeneas.Std Result

def bytes : List U8 := [34#u8,8#u8,198#u8,55#u8,61#u8,211#u8,19#u8,178#u8,242#u8,118#u8,165#u8,45#u8,20#u8,254#u8,147#u8,25#u8,55#u8,157#u8,211#u8,124#u8,152#u8,170#u8,59#u8,88#u8,182#u8,77#u8,252#u8,152#u8,45#u8,26#u8,82#u8,63#u8]
theorem length : bytes.length=32 := by simp only [bytes,List.length_cons,List.length_nil]

theorem selected : (NFY_JFx_NativeBytes.publicInput.val.drop 224).take 32=bytes := by
  change (NFY_JFx_DataPublic00.bytes.drop 224).take 32=bytes
  simp only [NFY_JFx_DataPublic00.bytes,NFY_JFx_DataPublic00.c00_length,NFY_JFx_DataPublic00.c01_length,NFY_JFx_DataPublic00.c02_length,NFY_JFx_DataPublic00.c03_length,NFY_JFx_DataPublic00.c04_length,NFY_JFx_DataPublic00.c05_length,NFY_JFx_DataPublic00.c06_length,NFY_JFx_DataPublic00.c07_length,NFY_JFx_DataPublic00.c08_length,NFY_JFx_DataPublic00.c09_length,NFY_JFx_DataPublic00.c10_length,NFY_JFx_DataPublic00.c11_length,NFY_JFx_DataPublic00.c12_length,NFY_JFx_DataPublic00.c13_length,NFY_JFx_DataPublic00.c14_length,NFY_JFx_DataPublic00.c15_length,NFY_JFx_DataPublic00.c16_length,NFY_JFx_DataPublic00.c17_length,NFY_JFx_DataPublic00.c18_length,NFY_JFx_DataPublic00.c19_length,NFY_JFx_DataPublic00.c20_length,NFY_JFx_DataPublic00.c21_length,NFY_JFx_DataPublic00.c22_length,NFY_JFx_DataPublic00.c23_length,NFY_JFx_DataPublic00.c24_length,NFY_JFx_DataPublic00.c25_length,NFY_JFx_DataPublic00.c26_length,NFY_JFx_DataPublic00.c27_length,NFY_JFx_DataPublic00.c28_length,NFY_JFx_DataPublic00.c29_length,NFY_JFx_DataPublic00.c30_length,NFY_JFx_DataPublic00.c31_length,NFY_JFx_DataPublic00.c32_length,NFY_JFx_DataPublic00.c33_length,NFY_JFx_DataPublic00.c34_length,NFY_JFx_DataPublic00.c35_length,NFY_JFx_DataPublic00.c36_length,NFY_JFx_DataPublic00.c37_length,NFY_JFx_DataPublic00.c38_length,NFY_JFx_DataPublic00.c39_length,NFY_JFx_DataPublic00.c40_length,NFY_JFx_DataPublic00.c41_length,NFY_JFx_DataPublic00.c42_length,NFY_JFx_DataPublic00.c43_length,NFY_JFx_DataPublic00.c44_length,NFY_JFx_DataPublic00.c45_length,NFY_JFx_DataPublic00.c46_length,NFY_JFx_DataPublic00.c47_length,NFY_JFx_DataPublic00.c48_length,NFY_JFx_DataPublic00.c49_length,NFY_JFx_DataPublic00.c50_length,NFY_JFx_DataPublic00.c51_length,NFY_JFx_DataPublic00.c52_length,NFY_JFx_DataPublic00.c53_length,NFY_JFx_DataPublic00.c54_length,NFY_JFx_DataPublic00.c55_length,NFY_JFx_DataPublic00.c56_length,NFY_JFx_DataPublic00.c57_length,NFY_JFx_DataPublic00.c58_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem source : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    NFY_JFx_NativeBytes.publicInput {start:=224#usize,«end»:=256#usize}=
    ok (NFY_JFu_PublicRange.segment 224 32 (by decide)) :=
  by
    have call:=NFY_JFu_PublicRange.read 224#usize 256#usize (by decide) (by decide)
    simpa only [show (224#usize).val=224 from rfl,
      show (256#usize).val=256 from rfl,Nat.reduceSub] using call

#print axioms length
#print axioms selected
#print axioms source
end AspisR1.NFY_JFu_PublicMeta02
-- END copied JFu_PublicMeta02
-- BEGIN copied JFu_PublicMeta03: lean/JFu_PublicMeta03.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFu_PublicMeta03
open Aeneas Aeneas.Std Result

def bytes : List U8 := [5#u8,5#u8,5#u8,5#u8,5#u8,5#u8,5#u8,5#u8,5#u8,5#u8,5#u8,5#u8,5#u8,5#u8,5#u8,5#u8,5#u8,5#u8,5#u8,5#u8,5#u8,5#u8,5#u8,5#u8,5#u8,5#u8,5#u8,5#u8,5#u8,5#u8,5#u8,5#u8]
theorem length : bytes.length=32 := by simp only [bytes,List.length_cons,List.length_nil]

theorem selected : (NFY_JFx_NativeBytes.publicInput.val.drop 256).take 32=bytes := by
  change (NFY_JFx_DataPublic00.bytes.drop 256).take 32=bytes
  simp only [NFY_JFx_DataPublic00.bytes,NFY_JFx_DataPublic00.c00_length,NFY_JFx_DataPublic00.c01_length,NFY_JFx_DataPublic00.c02_length,NFY_JFx_DataPublic00.c03_length,NFY_JFx_DataPublic00.c04_length,NFY_JFx_DataPublic00.c05_length,NFY_JFx_DataPublic00.c06_length,NFY_JFx_DataPublic00.c07_length,NFY_JFx_DataPublic00.c08_length,NFY_JFx_DataPublic00.c09_length,NFY_JFx_DataPublic00.c10_length,NFY_JFx_DataPublic00.c11_length,NFY_JFx_DataPublic00.c12_length,NFY_JFx_DataPublic00.c13_length,NFY_JFx_DataPublic00.c14_length,NFY_JFx_DataPublic00.c15_length,NFY_JFx_DataPublic00.c16_length,NFY_JFx_DataPublic00.c17_length,NFY_JFx_DataPublic00.c18_length,NFY_JFx_DataPublic00.c19_length,NFY_JFx_DataPublic00.c20_length,NFY_JFx_DataPublic00.c21_length,NFY_JFx_DataPublic00.c22_length,NFY_JFx_DataPublic00.c23_length,NFY_JFx_DataPublic00.c24_length,NFY_JFx_DataPublic00.c25_length,NFY_JFx_DataPublic00.c26_length,NFY_JFx_DataPublic00.c27_length,NFY_JFx_DataPublic00.c28_length,NFY_JFx_DataPublic00.c29_length,NFY_JFx_DataPublic00.c30_length,NFY_JFx_DataPublic00.c31_length,NFY_JFx_DataPublic00.c32_length,NFY_JFx_DataPublic00.c33_length,NFY_JFx_DataPublic00.c34_length,NFY_JFx_DataPublic00.c35_length,NFY_JFx_DataPublic00.c36_length,NFY_JFx_DataPublic00.c37_length,NFY_JFx_DataPublic00.c38_length,NFY_JFx_DataPublic00.c39_length,NFY_JFx_DataPublic00.c40_length,NFY_JFx_DataPublic00.c41_length,NFY_JFx_DataPublic00.c42_length,NFY_JFx_DataPublic00.c43_length,NFY_JFx_DataPublic00.c44_length,NFY_JFx_DataPublic00.c45_length,NFY_JFx_DataPublic00.c46_length,NFY_JFx_DataPublic00.c47_length,NFY_JFx_DataPublic00.c48_length,NFY_JFx_DataPublic00.c49_length,NFY_JFx_DataPublic00.c50_length,NFY_JFx_DataPublic00.c51_length,NFY_JFx_DataPublic00.c52_length,NFY_JFx_DataPublic00.c53_length,NFY_JFx_DataPublic00.c54_length,NFY_JFx_DataPublic00.c55_length,NFY_JFx_DataPublic00.c56_length,NFY_JFx_DataPublic00.c57_length,NFY_JFx_DataPublic00.c58_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem source : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    NFY_JFx_NativeBytes.publicInput {start:=256#usize,«end»:=288#usize}=
    ok (NFY_JFu_PublicRange.segment 256 32 (by decide)) :=
  by
    have call:=NFY_JFu_PublicRange.read 256#usize 288#usize (by decide) (by decide)
    simpa only [show (256#usize).val=256 from rfl,
      show (288#usize).val=288 from rfl,Nat.reduceSub] using call

#print axioms length
#print axioms selected
#print axioms source
end AspisR1.NFY_JFu_PublicMeta03
-- END copied JFu_PublicMeta03
-- BEGIN copied JFu_PublicBindings: lean/JFu_PublicBindings.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFu_PublicBindings
open Aeneas Aeneas.Std Result

def pool : Array U8 32#usize := ⟨NFY_JFu_PublicMeta02.bytes,NFY_JFu_PublicMeta02.length⟩
def domain : Array U8 32#usize := ⟨NFY_JFu_PublicMeta03.bytes,NFY_JFu_PublicMeta03.length⟩

theorem pool_selected : (NFY_JFx_NativeBytes.publicInput.val.drop 224).take 32=pool.val :=
  NFY_JFu_PublicMeta02.selected

theorem domain_selected : (NFY_JFx_NativeBytes.publicInput.val.drop 256).take 32=domain.val :=
  NFY_JFu_PublicMeta03.selected

/-- The source comparison short-circuits on the first unequal byte,34 versus0. -/
theorem pool_nonzero : core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8
    pool (Array.repeat 32#usize 0#u8)=ok false := by rfl

/-- The source comparison short-circuits on the first unequal byte,5 versus0. -/
theorem domain_nonzero : core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8
    domain (Array.repeat 32#usize 0#u8)=ok false := by rfl

#print axioms pool_selected
#print axioms domain_selected
#print axioms pool_nonzero
#print axioms domain_nonzero
end AspisR1.NFY_JFu_PublicBindings
-- END copied JFu_PublicBindings
-- BEGIN copied JFu_PublicMeta04: lean/JFu_PublicMeta04.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFu_PublicMeta04
open Aeneas Aeneas.Std Result

def bytes : List U8 := [13#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
theorem length : bytes.length=8 := by simp only [bytes,List.length_cons,List.length_nil]

theorem selected : (NFY_JFx_NativeBytes.publicInput.val.drop 288).take 8=bytes := by
  change (NFY_JFx_DataPublic00.bytes.drop 288).take 8=bytes
  simp only [NFY_JFx_DataPublic00.bytes,NFY_JFx_DataPublic00.c00_length,NFY_JFx_DataPublic00.c01_length,NFY_JFx_DataPublic00.c02_length,NFY_JFx_DataPublic00.c03_length,NFY_JFx_DataPublic00.c04_length,NFY_JFx_DataPublic00.c05_length,NFY_JFx_DataPublic00.c06_length,NFY_JFx_DataPublic00.c07_length,NFY_JFx_DataPublic00.c08_length,NFY_JFx_DataPublic00.c09_length,NFY_JFx_DataPublic00.c10_length,NFY_JFx_DataPublic00.c11_length,NFY_JFx_DataPublic00.c12_length,NFY_JFx_DataPublic00.c13_length,NFY_JFx_DataPublic00.c14_length,NFY_JFx_DataPublic00.c15_length,NFY_JFx_DataPublic00.c16_length,NFY_JFx_DataPublic00.c17_length,NFY_JFx_DataPublic00.c18_length,NFY_JFx_DataPublic00.c19_length,NFY_JFx_DataPublic00.c20_length,NFY_JFx_DataPublic00.c21_length,NFY_JFx_DataPublic00.c22_length,NFY_JFx_DataPublic00.c23_length,NFY_JFx_DataPublic00.c24_length,NFY_JFx_DataPublic00.c25_length,NFY_JFx_DataPublic00.c26_length,NFY_JFx_DataPublic00.c27_length,NFY_JFx_DataPublic00.c28_length,NFY_JFx_DataPublic00.c29_length,NFY_JFx_DataPublic00.c30_length,NFY_JFx_DataPublic00.c31_length,NFY_JFx_DataPublic00.c32_length,NFY_JFx_DataPublic00.c33_length,NFY_JFx_DataPublic00.c34_length,NFY_JFx_DataPublic00.c35_length,NFY_JFx_DataPublic00.c36_length,NFY_JFx_DataPublic00.c37_length,NFY_JFx_DataPublic00.c38_length,NFY_JFx_DataPublic00.c39_length,NFY_JFx_DataPublic00.c40_length,NFY_JFx_DataPublic00.c41_length,NFY_JFx_DataPublic00.c42_length,NFY_JFx_DataPublic00.c43_length,NFY_JFx_DataPublic00.c44_length,NFY_JFx_DataPublic00.c45_length,NFY_JFx_DataPublic00.c46_length,NFY_JFx_DataPublic00.c47_length,NFY_JFx_DataPublic00.c48_length,NFY_JFx_DataPublic00.c49_length,NFY_JFx_DataPublic00.c50_length,NFY_JFx_DataPublic00.c51_length,NFY_JFx_DataPublic00.c52_length,NFY_JFx_DataPublic00.c53_length,NFY_JFx_DataPublic00.c54_length,NFY_JFx_DataPublic00.c55_length,NFY_JFx_DataPublic00.c56_length,NFY_JFx_DataPublic00.c57_length,NFY_JFx_DataPublic00.c58_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem source : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    NFY_JFx_NativeBytes.publicInput {start:=288#usize,«end»:=296#usize}=
    ok (NFY_JFu_PublicRange.segment 288 8 (by decide)) :=
  by
    have call:=NFY_JFu_PublicRange.read 288#usize 296#usize (by decide) (by decide)
    simpa only [show (288#usize).val=288 from rfl,
      show (296#usize).val=296 from rfl,Nat.reduceSub] using call

#print axioms length
#print axioms selected
#print axioms source
end AspisR1.NFY_JFu_PublicMeta04
-- END copied JFu_PublicMeta04
-- BEGIN copied JFu_PublicMeta05: lean/JFu_PublicMeta05.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFu_PublicMeta05
open Aeneas Aeneas.Std Result

def bytes : List U8 := [13#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
theorem length : bytes.length=8 := by simp only [bytes,List.length_cons,List.length_nil]

theorem selected : (NFY_JFx_NativeBytes.publicInput.val.drop 296).take 8=bytes := by
  change (NFY_JFx_DataPublic00.bytes.drop 296).take 8=bytes
  simp only [NFY_JFx_DataPublic00.bytes,NFY_JFx_DataPublic00.c00_length,NFY_JFx_DataPublic00.c01_length,NFY_JFx_DataPublic00.c02_length,NFY_JFx_DataPublic00.c03_length,NFY_JFx_DataPublic00.c04_length,NFY_JFx_DataPublic00.c05_length,NFY_JFx_DataPublic00.c06_length,NFY_JFx_DataPublic00.c07_length,NFY_JFx_DataPublic00.c08_length,NFY_JFx_DataPublic00.c09_length,NFY_JFx_DataPublic00.c10_length,NFY_JFx_DataPublic00.c11_length,NFY_JFx_DataPublic00.c12_length,NFY_JFx_DataPublic00.c13_length,NFY_JFx_DataPublic00.c14_length,NFY_JFx_DataPublic00.c15_length,NFY_JFx_DataPublic00.c16_length,NFY_JFx_DataPublic00.c17_length,NFY_JFx_DataPublic00.c18_length,NFY_JFx_DataPublic00.c19_length,NFY_JFx_DataPublic00.c20_length,NFY_JFx_DataPublic00.c21_length,NFY_JFx_DataPublic00.c22_length,NFY_JFx_DataPublic00.c23_length,NFY_JFx_DataPublic00.c24_length,NFY_JFx_DataPublic00.c25_length,NFY_JFx_DataPublic00.c26_length,NFY_JFx_DataPublic00.c27_length,NFY_JFx_DataPublic00.c28_length,NFY_JFx_DataPublic00.c29_length,NFY_JFx_DataPublic00.c30_length,NFY_JFx_DataPublic00.c31_length,NFY_JFx_DataPublic00.c32_length,NFY_JFx_DataPublic00.c33_length,NFY_JFx_DataPublic00.c34_length,NFY_JFx_DataPublic00.c35_length,NFY_JFx_DataPublic00.c36_length,NFY_JFx_DataPublic00.c37_length,NFY_JFx_DataPublic00.c38_length,NFY_JFx_DataPublic00.c39_length,NFY_JFx_DataPublic00.c40_length,NFY_JFx_DataPublic00.c41_length,NFY_JFx_DataPublic00.c42_length,NFY_JFx_DataPublic00.c43_length,NFY_JFx_DataPublic00.c44_length,NFY_JFx_DataPublic00.c45_length,NFY_JFx_DataPublic00.c46_length,NFY_JFx_DataPublic00.c47_length,NFY_JFx_DataPublic00.c48_length,NFY_JFx_DataPublic00.c49_length,NFY_JFx_DataPublic00.c50_length,NFY_JFx_DataPublic00.c51_length,NFY_JFx_DataPublic00.c52_length,NFY_JFx_DataPublic00.c53_length,NFY_JFx_DataPublic00.c54_length,NFY_JFx_DataPublic00.c55_length,NFY_JFx_DataPublic00.c56_length,NFY_JFx_DataPublic00.c57_length,NFY_JFx_DataPublic00.c58_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem source : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    NFY_JFx_NativeBytes.publicInput {start:=296#usize,«end»:=304#usize}=
    ok (NFY_JFu_PublicRange.segment 296 8 (by decide)) :=
  by
    have call:=NFY_JFu_PublicRange.read 296#usize 304#usize (by decide) (by decide)
    simpa only [show (296#usize).val=296 from rfl,
      show (304#usize).val=304 from rfl,Nat.reduceSub] using call

#print axioms length
#print axioms selected
#print axioms source
end AspisR1.NFY_JFu_PublicMeta05
-- END copied JFu_PublicMeta05
-- BEGIN copied JFu_PublicIndices: lean/JFu_PublicIndices.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFu_PublicIndices
open Aeneas Aeneas.Std Result

def before : Array U8 8#usize := Array.make 8#usize [13#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def after : Array U8 8#usize := Array.make 8#usize [14#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]

theorem sequence_bytes : (NFY_JFx_NativeBytes.publicInput.val.drop 288).take 8=before.val :=
  NFY_JFu_PublicMeta04.selected

theorem index_bytes : (NFY_JFx_NativeBytes.publicInput.val.drop 296).take 8=before.val :=
  NFY_JFu_PublicMeta05.selected

theorem next_bytes : (NFY_JFx_NativeBytes.publicInput.val.drop 984).take 8=after.val := by
  have selected:=congrArg (fun xs : List U8 => (xs.drop 8).take 8) NFY_JFu_PublicMeta06.selected
  rw [NFY_JFu_PublicRange.nested _ 976 16 8 8 (by decide)] at selected
  exact selected

theorem sequence : core.num.U64.from_le_bytes before=13#u64 := by rfl
theorem next : core.num.U64.from_le_bytes after=14#u64 := by rfl

theorem advance : U64.checked_add (core.num.U64.from_le_bytes before) 1#u64=
    some (core.num.U64.from_le_bytes after) := by
  rw [sequence,next]
  rfl

#print axioms sequence_bytes
#print axioms index_bytes
#print axioms next_bytes
#print axioms sequence
#print axioms next
#print axioms advance
end AspisR1.NFY_JFu_PublicIndices
-- END copied JFu_PublicIndices
-- BEGIN copied JFt_Metadata: lean/JFt_Metadata.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFt_Metadata
open Aeneas Aeneas.Std Result

theorem pool : AspisS6NativeSnapshotReadArray.read_array 32#usize
    (NFY_JFu_PublicRange.segment 224 32 (by decide))=ok NFY_JFu_PublicBindings.pool :=
  NFY_JFt_ReadArray.source _ _ _ _ _ NFY_JFu_PublicBindings.pool_selected

theorem domain : AspisS6NativeSnapshotReadArray.read_array 32#usize
    (NFY_JFu_PublicRange.segment 256 32 (by decide))=ok NFY_JFu_PublicBindings.domain :=
  NFY_JFt_ReadArray.source _ _ _ _ _ NFY_JFu_PublicBindings.domain_selected

theorem sequence : AspisS6NativeSnapshotReadArray.read_array 8#usize
    (NFY_JFu_PublicRange.segment 288 8 (by decide))=ok NFY_JFu_PublicIndices.before :=
  NFY_JFt_ReadArray.source _ _ _ _ _ NFY_JFu_PublicIndices.sequence_bytes

theorem index : AspisS6NativeSnapshotReadArray.read_array 8#usize
    (NFY_JFu_PublicRange.segment 296 8 (by decide))=ok NFY_JFu_PublicIndices.before :=
  NFY_JFt_ReadArray.source _ _ _ _ _ NFY_JFu_PublicIndices.index_bytes

theorem next : AspisS6NativeSnapshotReadArray.read_array 8#usize
    (NFY_JFu_PublicRange.segment 984 8 (by decide))=ok NFY_JFu_PublicIndices.after :=
  NFY_JFt_ReadArray.source _ _ _ _ _ NFY_JFu_PublicIndices.next_bytes

#print axioms pool
#print axioms domain
#print axioms sequence
#print axioms index
#print axioms next
end AspisR1.NFY_JFt_Metadata
-- END copied JFt_Metadata

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
