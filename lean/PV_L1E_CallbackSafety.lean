import PV_L1E_Source_070
import PV_L1D_CallbackSafe
set_option autoImplicit false
noncomputable section
namespace PV_L1E_CallbackSafety
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1D_Logged PV_L1D_CallbackSafe
variable [ExternalTypes] [ExternalFuns]
theorem safe_coe {α : Type} (r : Result α) : Safe (r : Logged α) := rfl
#print axioms safe_coe
theorem safe_PV_L1D_Source_030
  (reserved : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets)
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (tag : Std.U8) :
  Safe (PV_L1D_Source_030.produce reserved context hash tag) := by
  unfold PV_L1D_Source_030.produce
  try simp only [PV_L1D_Projection.prod_case]
  repeat' first
    | exact safe_lift _
    | exact safe_coe _
    | exact safe_pure _
    | apply safe_observe; rfl
    | apply safe_bind
    | intro value
    | split <;> simp only [PV_L1D_Projection.prod_case]
#print axioms safe_PV_L1D_Source_030
theorem safe_PV_L1D_Source_003
  (out : alloc.vec.Vec Std.U8) (cc1 : host_commitment.Commitment)
  (cc2 : host_commitment.Commitment) (queries : Array Std.U32 22#usize)
  (folded_word : Slice aspis_core.field.wide_exact.WideExact)
  (folded_salts : host_commitment.PrivateSalts) :
  Safe (PV_L1D_Source_003.produce out cc1 cc2 queries folded_word folded_salts) := by
  unfold PV_L1D_Source_003.produce
  try simp only [PV_L1D_Projection.prod_case]
  repeat' first
    | exact safe_lift _
    | exact safe_coe _
    | exact safe_pure _
    | apply safe_observe; rfl
    | apply safe_bind
    | intro value
    | split <;> simp only [PV_L1D_Projection.prod_case]
#print axioms safe_PV_L1D_Source_003
theorem safe_PV_L1D_Source_004
  (queries : Array Std.U32 22#usize) (begin1 : Std.Usize) (end1 : Std.Usize)
  (folded : Bool) :
  Safe (PV_L1D_Source_004.produce queries begin1 end1 folded) := by
  unfold PV_L1D_Source_004.produce
  try simp only [PV_L1D_Projection.prod_case]
  repeat' first
    | exact safe_lift _
    | exact safe_coe _
    | exact safe_pure _
    | apply safe_observe; rfl
    | apply safe_bind
    | intro value
    | split <;> simp only [PV_L1D_Projection.prod_case]
#print axioms safe_PV_L1D_Source_004
theorem safe_PV_L1D_Source_005
  (out : alloc.vec.Vec Std.U8) (cc1 : host_commitment.Commitment)
  (cc2 : host_commitment.Commitment) (tree : host_tree.BinaryTree)
  (queries : Array Std.U32 22#usize) (batch : Std.Usize) (t : Std.Usize) :
  Safe (PV_L1D_Source_005.produce out cc1 cc2 tree queries batch t) := by
  unfold PV_L1D_Source_005.produce
  try simp only [PV_L1D_Projection.prod_case]
  repeat' first
    | solve | apply safe_PV_L1D_Source_004
    | exact safe_lift _
    | exact safe_coe _
    | exact safe_pure _
    | apply safe_observe; rfl
    | apply safe_bind
    | intro value
    | split <;> simp only [PV_L1D_Projection.prod_case]
#print axioms safe_PV_L1D_Source_005
theorem safe_PV_L1D_Source_006
  (out : alloc.vec.Vec Std.U8) (cc1 : host_commitment.Commitment)
  (cc2 : host_commitment.Commitment) (tree : host_tree.BinaryTree)
  (queries : Array Std.U32 22#usize) :
  Safe (PV_L1D_Source_006.produce out cc1 cc2 tree queries) := by
  unfold PV_L1D_Source_006.produce
  try simp only [PV_L1D_Projection.prod_case]
  repeat' first
    | solve | apply safe_PV_L1D_Source_005
    | exact safe_lift _
    | exact safe_coe _
    | exact safe_pure _
    | apply safe_observe; rfl
    | apply safe_bind
    | intro value
    | split <;> simp only [PV_L1D_Projection.prod_case]
#print axioms safe_PV_L1D_Source_006
theorem safe_PV_L1D_Source_007
  (variant : transport.Variant) (p : prover.Publication) :
  Safe (PV_L1D_Source_007.produce variant p) := by
  unfold PV_L1D_Source_007.produce
  try simp only [PV_L1D_Projection.prod_case]
  repeat' first
    | solve | apply safe_PV_L1D_Source_006
    | solve | apply safe_PV_L1D_Source_003
    | exact safe_lift _
    | exact safe_coe _
    | exact safe_pure _
    | apply safe_observe; rfl
    | apply safe_bind
    | intro value
    | split <;> simp only [PV_L1D_Projection.prod_case]
#print axioms safe_PV_L1D_Source_007
theorem safe_PV_L1D_QueryAbsorb
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (self : host_transcript.Transcript H) (row : Std.U8) (payload : Slice Std.U8) :
  Safe (PV_L1D_QueryAbsorb.produce aspis_coredigestDigest32Inst self row payload) := by
  unfold PV_L1D_QueryAbsorb.produce
  try simp only [PV_L1D_Projection.prod_case]
  repeat' first
    | exact safe_lift _
    | exact safe_coe _
    | exact safe_pure _
    | apply safe_observe; rfl
    | apply safe_bind
    | intro value
    | split <;> simp only [PV_L1D_Projection.prod_case]
#print axioms safe_PV_L1D_QueryAbsorb
theorem safe_PV_L1D_QueryProducer
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (self : host_transcript.Transcript H) (row : Std.U8) (payload : Slice Std.U8) :
  Safe (PV_L1D_QueryProducer.produce aspis_coredigestDigest32Inst self row payload) := by
  unfold PV_L1D_QueryProducer.produce
  try simp only [PV_L1D_Projection.prod_case]
  repeat' first
    | solve | apply safe_PV_L1D_QueryAbsorb
    | exact safe_lift _
    | exact safe_coe _
    | exact safe_pure _
    | apply safe_observe; rfl
    | apply safe_bind
    | intro value
    | split <;> simp only [PV_L1D_Projection.prod_case]
#print axioms safe_PV_L1D_QueryProducer
theorem safe_PV_L1D_Source_008
  (variant : transport.Variant)
  (challenges : aspis_z4b_probe.probe.z9.z9b.z9c.z9d.z9e.R1PublicChallenges)
  (c1_root : Array Std.U8 32#usize) :
  Safe (PV_L1D_Source_008.produce variant challenges c1_root) := by
  unfold PV_L1D_Source_008.produce
  try simp only [PV_L1D_Projection.prod_case]
  repeat' first
    | exact safe_lift _
    | exact safe_coe _
    | exact safe_pure _
    | apply safe_observe; rfl
    | apply safe_bind
    | intro value
    | split <;> simp only [PV_L1D_Projection.prod_case]
#print axioms safe_PV_L1D_Source_008
theorem safe_PV_L1D_Source_009
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (word : Slice aspis_core.field.wide_exact.WideExact)
  (salts : host_commitment.PrivateSalts) :
  Safe (PV_L1D_Source_009.produce hash word salts) := by
  unfold PV_L1D_Source_009.produce
  try simp only [PV_L1D_Projection.prod_case]
  repeat' first
    | exact safe_lift _
    | exact safe_coe _
    | exact safe_pure _
    | apply safe_observe; rfl
    | apply safe_bind
    | intro value
    | split <;> simp only [PV_L1D_Projection.prod_case]
#print axioms safe_PV_L1D_Source_009
theorem safe_PV_L1D_Source_015
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (self : host_transcript.Transcript H) (row : Std.U8) (payload : Slice Std.U8) :
  Safe (PV_L1D_Source_015.produce (H := H) aspis_coredigestDigest32Inst self row payload) := by
  unfold PV_L1D_Source_015.produce
  try simp only [PV_L1D_Projection.prod_case]
  repeat' first
    | exact safe_lift _
    | exact safe_coe _
    | exact safe_pure _
    | apply safe_observe; rfl
    | apply safe_bind
    | intro value
    | split <;> simp only [PV_L1D_Projection.prod_case]
#print axioms safe_PV_L1D_Source_015
theorem safe_PV_L1D_Source_017
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (self : host_transcript.Transcript H) (row : Std.U8) (payload : Slice Std.U8) :
  Safe (PV_L1D_Source_017.produce (H := H) aspis_coredigestDigest32Inst self row payload) := by
  unfold PV_L1D_Source_017.produce
  try simp only [PV_L1D_Projection.prod_case]
  repeat' first
    | solve | apply safe_PV_L1D_Source_015
    | exact safe_lift _
    | exact safe_coe _
    | exact safe_pure _
    | apply safe_observe; rfl
    | apply safe_bind
    | intro value
    | split <;> simp only [PV_L1D_Projection.prod_case]
#print axioms safe_PV_L1D_Source_017
theorem safe_PV_L1D_Source_018
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (self : host_transcript.Transcript H) (row : Std.U8) (payload : Slice Std.U8) :
  Safe (PV_L1D_Source_018.produce (H := H) aspis_coredigestDigest32Inst self row payload) := by
  unfold PV_L1D_Source_018.produce
  try simp only [PV_L1D_Projection.prod_case]
  repeat' first
    | solve | apply safe_PV_L1D_Source_017
    | exact safe_lift _
    | exact safe_coe _
    | exact safe_pure _
    | apply safe_observe; rfl
    | apply safe_bind
    | intro value
    | split <;> simp only [PV_L1D_Projection.prod_case]
#print axioms safe_PV_L1D_Source_018
theorem safe_PV_L1D_Source_019
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (self : host_transcript.Transcript H) (row : Std.U8) (payload : Slice Std.U8)
  (nonzero : Bool) :
  Safe (PV_L1D_Source_019.produce (H := H) aspis_coredigestDigest32Inst self row payload nonzero) := by
  unfold PV_L1D_Source_019.produce
  try simp only [PV_L1D_Projection.prod_case]
  repeat' first
    | solve | apply safe_PV_L1D_Source_017
    | exact safe_lift _
    | exact safe_coe _
    | exact safe_pure _
    | apply safe_observe; rfl
    | apply safe_bind
    | intro value
    | split <;> simp only [PV_L1D_Projection.prod_case]
#print axioms safe_PV_L1D_Source_019
theorem safe_PV_L1D_Source_020
  (variant : transport.Variant)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (prepared : prover.PreparedOpening)
  (folded_salts : host_commitment.PrivateSalts) :
  Safe (PV_L1D_Source_020.produce variant hash prepared folded_salts) := by
  unfold PV_L1D_Source_020.produce
  try simp only [PV_L1D_Projection.prod_case]
  repeat' first
    | solve | apply safe_PV_L1D_Source_019
    | solve | apply safe_PV_L1D_Source_018
    | solve | apply safe_PV_L1D_Source_009
    | solve | apply safe_PV_L1D_Source_008
    | solve | apply safe_PV_L1D_QueryProducer
    | exact safe_lift _
    | exact safe_coe _
    | exact safe_pure _
    | apply safe_observe; rfl
    | apply safe_bind
    | intro value
    | split <;> simp only [PV_L1D_Projection.prod_case]
#print axioms safe_PV_L1D_Source_020
theorem safe_PV_L1D_Source_021
  (q : Slice aspis_core.field.wide_exact.WideExact) (w : weights.Weights) :
  Safe (PV_L1D_Source_021.produce q w) := by
  unfold PV_L1D_Source_021.produce
  try simp only [PV_L1D_Projection.prod_case]
  repeat' first
    | exact safe_lift _
    | exact safe_coe _
    | exact safe_pure _
    | apply safe_observe; rfl
    | apply safe_bind
    | intro value
    | split <;> simp only [PV_L1D_Projection.prod_case]
#print axioms safe_PV_L1D_Source_021
theorem safe_PV_L1D_Source_023
  (coefficients : Slice (Array aspis_core.field.wide_exact.WideExact
  1024#usize)) (gamma : aspis_core.field.wide_exact.WideExact) :
  Safe (PV_L1D_Source_023.produce coefficients gamma) := by
  unfold PV_L1D_Source_023.produce
  try simp only [PV_L1D_Projection.prod_case]
  repeat' first
    | exact safe_lift _
    | exact safe_coe _
    | exact safe_pure _
    | apply safe_observe; rfl
    | apply safe_bind
    | intro value
    | split <;> simp only [PV_L1D_Projection.prod_case]
#print axioms safe_PV_L1D_Source_023
theorem safe_PV_L1D_Source_024
  (coefficients : Slice (Array aspis_core.field.wide_exact.WideExact
  1024#usize))
  (z1 : aspis_core.r0.domain.Point aspis_core.field.wide_exact.WideExact) :
  Safe (PV_L1D_Source_024.produce coefficients z1) := by
  unfold PV_L1D_Source_024.produce
  try simp only [PV_L1D_Projection.prod_case]
  repeat' first
    | exact safe_lift _
    | exact safe_coe _
    | exact safe_pure _
    | apply safe_observe; rfl
    | apply safe_bind
    | intro value
    | split <;> simp only [PV_L1D_Projection.prod_case]
#print axioms safe_PV_L1D_Source_024
theorem safe_PV_L1D_Source_025
  (variant : transport.Variant)
  (messages : Slice (Array aspis_core.field.wide_exact.WideExact 1024#usize)) :
  Safe (PV_L1D_Source_025.produce variant messages) := by
  unfold PV_L1D_Source_025.produce
  try simp only [PV_L1D_Projection.prod_case]
  repeat' first
    | exact safe_lift _
    | exact safe_coe _
    | exact safe_pure _
    | apply safe_observe; rfl
    | apply safe_bind
    | intro value
    | split <;> simp only [PV_L1D_Projection.prod_case]
#print axioms safe_PV_L1D_Source_025
theorem safe_PV_L1D_Source_026
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (hash : H) (semantic_state : Array Std.U8 32#usize)
  (variant : transport.Variant) :
  Safe (PV_L1D_Source_026.produce (H := H) aspis_coredigestDigest32Inst hash semantic_state variant) := by
  unfold PV_L1D_Source_026.produce
  try simp only [PV_L1D_Projection.prod_case]
  repeat' first
    | exact safe_lift _
    | exact safe_coe _
    | exact safe_pure _
    | apply safe_observe; rfl
    | apply safe_bind
    | intro value
    | split <;> simp only [PV_L1D_Projection.prod_case]
#print axioms safe_PV_L1D_Source_026
theorem safe_PV_L1D_Source_027
  (variant : transport.Variant)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (backend : prover.Backend)
  (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn) :
  Safe (PV_L1D_Source_027.produce variant hash backend sem) := by
  unfold PV_L1D_Source_027.produce
  try simp only [PV_L1D_Projection.prod_case]
  repeat' first
    | solve | apply safe_PV_L1D_Source_026
    | solve | apply safe_PV_L1D_Source_025
    | solve | apply safe_PV_L1D_Source_024
    | solve | apply safe_PV_L1D_Source_023
    | solve | apply safe_PV_L1D_Source_021
    | solve | apply safe_PV_L1D_Source_019
    | exact safe_lift _
    | exact safe_coe _
    | exact safe_pure _
    | apply safe_observe; rfl
    | apply safe_bind
    | intro value
    | split <;> simp only [PV_L1D_Projection.prod_case]
#print axioms safe_PV_L1D_Source_027
theorem safe_PV_L1D_Source_031
  (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (variant : transport.Variant)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (backend : prover.Backend)
  (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn)
  (salts : (aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets ×
  aspis_core.state_only_hiding.StateOnlyHidingContext)) :
  Safe (PV_L1D_Source_031.produce public1 variant hash backend sem salts) := by
  unfold PV_L1D_Source_031.produce
  try simp only [PV_L1D_Projection.prod_case]
  repeat' first
    | solve | apply safe_PV_L1D_Source_027
    | solve | apply safe_PV_L1D_Source_020
    | solve | apply safe_PV_L1D_Source_007
    | solve | apply safe_PV_L1D_Source_030
    | exact safe_lift _
    | exact safe_coe _
    | exact safe_pure _
    | apply safe_observe; rfl
    | apply safe_bind
    | intro value
    | split <;> simp only [PV_L1D_Projection.prod_case]
#print axioms safe_PV_L1D_Source_031
theorem safe_PV_L1D_Source_033
  (values : Slice aspis_core.field.QM31) (masks : Array Std.U16 64#usize) :
  Safe (PV_L1D_Source_033.produce values masks) := by
  unfold PV_L1D_Source_033.produce
  try simp only [PV_L1D_Projection.prod_case]
  repeat' first
    | exact safe_lift _
    | exact safe_coe _
    | exact safe_pure _
    | apply safe_observe; rfl
    | apply safe_bind
    | intro value
    | split <;> simp only [PV_L1D_Projection.prod_case]
#print axioms safe_PV_L1D_Source_033
theorem safe_PV_L1D_Source_037
  (c1 : Slice (alloc.vec.Vec aspis_core.field.M31))
  (mask_only : Array (alloc.vec.Vec aspis_core.field.M31) 10#usize)
  (d : Array aspis_core.field.QM31 1024#usize)
  (g : Array aspis_core.field.QM31 1024#usize)
  (h1_padding : Array aspis_core.field.QM31 1024#usize)
  (masks : Array Std.U16 64#usize) :
  Safe (PV_L1D_Source_037.produce c1 mask_only d g h1_padding masks) := by
  unfold PV_L1D_Source_037.produce
  try simp only [PV_L1D_Projection.prod_case]
  repeat' first
    | solve | apply safe_PV_L1D_Source_033
    | exact safe_lift _
    | exact safe_coe _
    | exact safe_pure _
    | apply safe_observe; rfl
    | apply safe_bind
    | intro value
    | split <;> simp only [PV_L1D_Projection.prod_case]
#print axioms safe_PV_L1D_Source_037
theorem safe_PV_L1D_Source_038
  (values : Slice aspis_core.field.QM31) :
  Safe (PV_L1D_Source_038.produce values) := by
  unfold PV_L1D_Source_038.produce
  try simp only [PV_L1D_Projection.prod_case]
  repeat' first
    | exact safe_lift _
    | exact safe_coe _
    | exact safe_pure _
    | apply safe_observe; rfl
    | apply safe_bind
    | intro value
    | split <;> simp only [PV_L1D_Projection.prod_case]
#print axioms safe_PV_L1D_Source_038
theorem safe_PV_L1D_Source_039
  (noised : Slice (alloc.vec.Vec aspis_core.field.M31))
  (mask_only : Array (alloc.vec.Vec aspis_core.field.M31) 10#usize) :
  Safe (PV_L1D_Source_039.produce noised mask_only) := by
  unfold PV_L1D_Source_039.produce
  try simp only [PV_L1D_Projection.prod_case]
  repeat' first
    | exact safe_lift _
    | exact safe_coe _
    | exact safe_pure _
    | apply safe_observe; rfl
    | apply safe_bind
    | intro value
    | split <;> simp only [PV_L1D_Projection.prod_case]
#print axioms safe_PV_L1D_Source_039
theorem safe_PV_L1D_Source_041
  {H : Type} {F : Type} (aspis_coredigestDigest32Inst :
  aspis_core.digest.Digest32 H) (OracleInst : host_sumcheck.Oracle F)
  (transcript : host_wire.SemanticTranscript H) (output : alloc.vec.Vec Std.U8)
  (point : Array aspis_core.field.QM31 10#usize)
  (running : aspis_core.field.QM31) (round : Std.Usize) (oracle : F) :
  Safe (PV_L1D_Source_041.produce (H := H) (F := F) aspis_coredigestDigest32Inst OracleInst transcript output point running round oracle) := by
  unfold PV_L1D_Source_041.produce
  try simp only [PV_L1D_Projection.prod_case]
  repeat' first
    | exact safe_lift _
    | exact safe_coe _
    | exact safe_pure _
    | apply safe_observe; rfl
    | apply safe_bind
    | intro value
    | split <;> simp only [PV_L1D_Projection.prod_case]
#print axioms safe_PV_L1D_Source_041
theorem safe_PV_L1D_Source_042
  {H : Type} {F : Type} (aspis_coredigestDigest32Inst :
  aspis_core.digest.Digest32 H) (OracleInst : host_sumcheck.Oracle F)
  (transcript : host_wire.SemanticTranscript H) (output : alloc.vec.Vec Std.U8)
  (point : Array aspis_core.field.QM31 10#usize)
  (running : aspis_core.field.QM31) (round : Std.Usize) (oracle : F) :
  Safe (PV_L1D_Source_042.produce (H := H) (F := F) aspis_coredigestDigest32Inst OracleInst transcript output point running round oracle) := by
  unfold PV_L1D_Source_042.produce
  try simp only [PV_L1D_Projection.prod_case]
  repeat' first
    | solve | apply safe_PV_L1D_Source_041
    | exact safe_lift _
    | exact safe_coe _
    | exact safe_pure _
    | apply safe_observe; rfl
    | apply safe_bind
    | intro value
    | split <;> simp only [PV_L1D_Projection.prod_case]
#print axioms safe_PV_L1D_Source_042
theorem safe_PV_L1D_Source_043
  {H : Type} {T1 : Type} (aspis_coredigestDigest32Inst :
  aspis_core.digest.Digest32 H) (OracleInst : host_sumcheck.Oracle T1)
  (transcript : host_wire.SemanticTranscript H) (output : alloc.vec.Vec Std.U8)
  (initial_claim : aspis_core.field.QM31) (oracle : T1) :
  Safe (PV_L1D_Source_043.produce (H := H) (T1 := T1) aspis_coredigestDigest32Inst OracleInst transcript output initial_claim oracle) := by
  unfold PV_L1D_Source_043.produce
  try simp only [PV_L1D_Projection.prod_case]
  repeat' first
    | solve | apply safe_PV_L1D_Source_042
    | exact safe_lift _
    | exact safe_coe _
    | exact safe_pure _
    | apply safe_observe; rfl
    | apply safe_bind
    | intro value
    | split <;> simp only [PV_L1D_Projection.prod_case]
#print axioms safe_PV_L1D_Source_043
theorem safe_PV_L1D_Source_044
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (row : Std.U8) (payload : Slice Std.U8)
  (transcript : host_wire.SemanticTranscript H) (bytes : alloc.vec.Vec Std.U8) :
  Safe (PV_L1D_Source_044.produce (H := H) aspis_coredigestDigest32Inst row payload transcript bytes) := by
  unfold PV_L1D_Source_044.produce
  try simp only [PV_L1D_Projection.prod_case]
  repeat' first
    | exact safe_lift _
    | exact safe_coe _
    | exact safe_pure _
    | apply safe_observe; rfl
    | apply safe_bind
    | intro value
    | split <;> simp only [PV_L1D_Projection.prod_case]
#print axioms safe_PV_L1D_Source_044
theorem safe_PV_L1D_Source_045
  (columns : Array (alloc.vec.Vec aspis_core.field.QM31) 29#usize)
  (variant : transport.Variant) (z : aspis_core.circle.SecureCirclePoint) :
  Safe (PV_L1D_Source_045.produce columns variant z) := by
  unfold PV_L1D_Source_045.produce
  try simp only [PV_L1D_Projection.prod_case]
  repeat' first
    | exact safe_lift _
    | exact safe_coe _
    | exact safe_pure _
    | apply safe_observe; rfl
    | apply safe_bind
    | intro value
    | split <;> simp only [PV_L1D_Projection.prod_case]
#print axioms safe_PV_L1D_Source_045
theorem safe_PV_L1D_Source_046
  (bytes : alloc.vec.Vec Std.U8)
  (claims : Array aspis_core.field.QM31 29#usize) :
  Safe (PV_L1D_Source_046.produce bytes claims) := by
  unfold PV_L1D_Source_046.produce
  try simp only [PV_L1D_Projection.prod_case]
  repeat' first
    | exact safe_lift _
    | exact safe_coe _
    | exact safe_pure _
    | apply safe_observe; rfl
    | apply safe_bind
    | intro value
    | split <;> simp only [PV_L1D_Projection.prod_case]
#print axioms safe_PV_L1D_Source_046
theorem safe_PV_L1D_Source_047
  (claims : Array (Array aspis_core.field.QM31 29#usize) 3#usize)
  (extras : Array aspis_core.field.QM31 29#usize) :
  Safe (PV_L1D_Source_047.produce claims extras) := by
  unfold PV_L1D_Source_047.produce
  try simp only [PV_L1D_Projection.prod_case]
  repeat' first
    | solve | apply safe_PV_L1D_Source_046
    | exact safe_lift _
    | exact safe_coe _
    | exact safe_pure _
    | apply safe_observe; rfl
    | apply safe_bind
    | intro value
    | split <;> simp only [PV_L1D_Projection.prod_case]
#print axioms safe_PV_L1D_Source_047
theorem safe_PV_L1D_Source_049
  (columns : Array (alloc.vec.Vec aspis_core.field.QM31) 29#usize)
  (variant : transport.Variant) (a : aspis_core.field.QM31)
  (b : aspis_core.field.QM31) :
  Safe (PV_L1D_Source_049.produce columns variant a b) := by
  unfold PV_L1D_Source_049.produce
  try simp only [PV_L1D_Projection.prod_case]
  repeat' first
    | exact safe_lift _
    | exact safe_coe _
    | exact safe_pure _
    | apply safe_observe; rfl
    | apply safe_bind
    | intro value
    | split <;> simp only [PV_L1D_Projection.prod_case]
#print axioms safe_PV_L1D_Source_049
theorem safe_PV_L1D_Source_051
  (columns : Array (alloc.vec.Vec aspis_core.field.QM31) 29#usize) :
  Safe (PV_L1D_Source_051.produce columns) := by
  unfold PV_L1D_Source_051.produce
  try simp only [PV_L1D_Projection.prod_case]
  repeat' first
    | exact safe_lift _
    | exact safe_coe _
    | exact safe_pure _
    | apply safe_observe; rfl
    | apply safe_bind
    | intro value
    | split <;> simp only [PV_L1D_Projection.prod_case]
#print axioms safe_PV_L1D_Source_051
theorem safe_PV_L1D_Source_052
  (c1 : Array (alloc.vec.Vec aspis_core.field.M31) 26#usize)
  (h1 : alloc.vec.Vec aspis_core.field.QM31)
  (g : Array aspis_core.field.QM31 1024#usize)
  (d : Array aspis_core.field.QM31 1024#usize) :
  Safe (PV_L1D_Source_052.produce c1 h1 g d) := by
  unfold PV_L1D_Source_052.produce
  try simp only [PV_L1D_Projection.prod_case]
  repeat' first
    | exact safe_lift _
    | exact safe_coe _
    | exact safe_pure _
    | apply safe_observe; rfl
    | apply safe_bind
    | intro value
    | split <;> simp only [PV_L1D_Projection.prod_case]
#print axioms safe_PV_L1D_Source_052
theorem safe_PV_L1D_Source_053
  (dc : Array aspis_core.field.QM31 1024#usize) (offset : Std.Usize)
  (j : Std.Usize) (sum : aspis_core.field.QM31) :
  Safe (PV_L1D_Source_053.produce dc offset j sum) := by
  unfold PV_L1D_Source_053.produce
  try simp only [PV_L1D_Projection.prod_case]
  repeat' first
    | exact safe_lift _
    | exact safe_coe _
    | exact safe_pure _
    | apply safe_observe; rfl
    | apply safe_bind
    | intro value
    | split <;> simp only [PV_L1D_Projection.prod_case]
#print axioms safe_PV_L1D_Source_053
theorem safe_PV_L1D_Source_054
  (dc : Array aspis_core.field.QM31 1024#usize) (offset : Std.Usize) :
  Safe (PV_L1D_Source_054.produce dc offset) := by
  unfold PV_L1D_Source_054.produce
  try simp only [PV_L1D_Projection.prod_case]
  repeat' first
    | solve | apply safe_PV_L1D_Source_053
    | exact safe_lift _
    | exact safe_coe _
    | exact safe_pure _
    | apply safe_observe; rfl
    | apply safe_bind
    | intro value
    | split <;> simp only [PV_L1D_Projection.prod_case]
#print axioms safe_PV_L1D_Source_054
theorem safe_PV_L1D_Source_055
  (mask_sum : aspis_core.field.QM31)
  (dc : Array aspis_core.field.QM31 1024#usize) :
  Safe (PV_L1D_Source_055.produce mask_sum dc) := by
  unfold PV_L1D_Source_055.produce
  try simp only [PV_L1D_Projection.prod_case]
  repeat' first
    | solve | apply safe_PV_L1D_Source_054
    | exact safe_lift _
    | exact safe_coe _
    | exact safe_pure _
    | apply safe_observe; rfl
    | apply safe_bind
    | intro value
    | split <;> simp only [PV_L1D_Projection.prod_case]
#print axioms safe_PV_L1D_Source_055
theorem safe_PV_L1D_Source_056
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (transcript : host_wire.SemanticTranscript H) (bytes : alloc.vec.Vec Std.U8) :
  Safe (PV_L1D_Source_056.produce (H := H) aspis_coredigestDigest32Inst transcript bytes) := by
  unfold PV_L1D_Source_056.produce
  try simp only [PV_L1D_Projection.prod_case]
  repeat' first
    | exact safe_lift _
    | exact safe_coe _
    | exact safe_pure _
    | apply safe_observe; rfl
    | apply safe_bind
    | intro value
    | split <;> simp only [PV_L1D_Projection.prod_case]
#print axioms safe_PV_L1D_Source_056
theorem safe_PV_L1D_Source_058
  (column : Array aspis_core.field.QM31 1024#usize) :
  Safe (PV_L1D_Source_058.produce column) := by
  unfold PV_L1D_Source_058.produce
  try simp only [PV_L1D_Projection.prod_case]
  repeat' first
    | exact safe_lift _
    | exact safe_coe _
    | exact safe_pure _
    | apply safe_observe; rfl
    | apply safe_bind
    | intro value
    | split <;> simp only [PV_L1D_Projection.prod_case]
#print axioms safe_PV_L1D_Source_058
theorem safe_PV_L1D_Source_062
  (c1 : Array (alloc.vec.Vec aspis_core.field.M31) 26#usize) :
  Safe (PV_L1D_Source_062.produce c1) := by
  unfold PV_L1D_Source_062.produce
  try simp only [PV_L1D_Projection.prod_case]
  repeat' first
    | exact safe_lift _
    | exact safe_coe _
    | exact safe_pure _
    | apply safe_observe; rfl
    | apply safe_bind
    | intro value
    | split <;> simp only [PV_L1D_Projection.prod_case]
#print axioms safe_PV_L1D_Source_062
theorem safe_PV_L1D_Source_063
  (c1 : Array (alloc.vec.Vec aspis_core.field.M31) 26#usize)
  (d : Array aspis_core.field.QM31 1024#usize)
  (g : Array aspis_core.field.QM31 1024#usize) :
  Safe (PV_L1D_Source_063.produce c1 d g) := by
  unfold PV_L1D_Source_063.produce
  try simp only [PV_L1D_Projection.prod_case]
  repeat' first
    | solve | apply safe_PV_L1D_Source_062
    | solve | apply safe_PV_L1D_Source_058
    | exact safe_lift _
    | exact safe_coe _
    | exact safe_pure _
    | apply safe_observe; rfl
    | apply safe_bind
    | intro value
    | split <;> simp only [PV_L1D_Projection.prod_case]
#print axioms safe_PV_L1D_Source_063
theorem safe_PV_L1D_Source_065
  (columns : Array (alloc.vec.Vec aspis_core.field.QM31) 29#usize)
  (point : Array aspis_core.field.QM31 10#usize) :
  Safe (PV_L1D_Source_065.produce columns point) := by
  unfold PV_L1D_Source_065.produce
  try simp only [PV_L1D_Projection.prod_case]
  repeat' first
    | exact safe_lift _
    | exact safe_coe _
    | exact safe_pure _
    | apply safe_observe; rfl
    | apply safe_bind
    | intro value
    | split <;> simp only [PV_L1D_Projection.prod_case]
#print axioms safe_PV_L1D_Source_065
theorem safe_PV_L1D_Source_066
  (columns : Array (alloc.vec.Vec aspis_core.field.QM31) 29#usize)
  (point : Array aspis_core.field.QM31 10#usize) :
  Safe (PV_L1D_Source_066.produce columns point) := by
  unfold PV_L1D_Source_066.produce
  try simp only [PV_L1D_Projection.prod_case]
  repeat' first
    | solve | apply safe_PV_L1D_Source_065
    | exact safe_lift _
    | exact safe_coe _
    | exact safe_pure _
    | apply safe_observe; rfl
    | apply safe_bind
    | intro value
    | split <;> simp only [PV_L1D_Projection.prod_case]
#print axioms safe_PV_L1D_Source_066
theorem safe_PV_L1D_Source_067
  {H : Type} {T1 : Type} {T2 : Type} (aspis_coredigestDigest32Inst :
  aspis_core.digest.Digest32 H)
  (coreopsfunctionFnOnceT1PairQM31QM31ResultVecQM31ErrorInst :
  core.ops.function.FnOnce T1 (aspis_core.field.QM31 × aspis_core.field.QM31)
  (core.result.Result (alloc.vec.Vec aspis_core.field.QM31) r1_wire.Error))
  (CommitmentsInst : host_semantic.Commitments T2)
  (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (c1 : Array (alloc.vec.Vec aspis_core.field.M31) 26#usize)
  (d : Array aspis_core.field.QM31 1024#usize)
  (g : Array aspis_core.field.QM31 1024#usize)
  (h1_padding : Array aspis_core.field.QM31 1024#usize) (helper : T1)
  (commitments : T2) (hash : H) (variant : transport.Variant) :
  Safe (PV_L1D_Source_067.produce (H := H) (T1 := T1) (T2 := T2) aspis_coredigestDigest32Inst coreopsfunctionFnOnceT1PairQM31QM31ResultVecQM31ErrorInst CommitmentsInst public1 c1 d g h1_padding helper commitments hash variant) := by
  unfold PV_L1D_Source_067.produce
  try simp only [PV_L1D_Projection.prod_case]
  repeat' first
    | solve | apply safe_PV_L1D_Source_066
    | solve | apply safe_PV_L1D_Source_063
    | solve | apply safe_PV_L1D_Source_056
    | solve | apply safe_PV_L1D_Source_055
    | solve | apply safe_PV_L1D_Source_052
    | solve | apply safe_PV_L1D_Source_051
    | solve | apply safe_PV_L1D_Source_049
    | solve | apply safe_PV_L1D_Source_047
    | solve | apply safe_PV_L1D_Source_045
    | solve | apply safe_PV_L1D_Source_044
    | solve | apply safe_PV_L1D_Source_043
    | exact safe_lift _
    | exact safe_coe _
    | exact safe_pure _
    | apply safe_observe; rfl
    | apply safe_bind
    | intro value
    | split <;> simp only [PV_L1D_Projection.prod_case]
#print axioms safe_PV_L1D_Source_067
theorem safe_PV_L1D_Source_068
  {H : Type} {T1 : Type} (aspis_coredigestDigest32Inst :
  aspis_core.digest.Digest32 H) (CommitmentsInst : host_semantic.Commitments
  T1)
  (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (compiled :
  aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
  (noised_semantic_c1 :
  aspis_statement.state_only_trace.StateOnlyTraceFoundation)
  (mask_only : Array (alloc.vec.Vec aspis_core.field.M31) 10#usize)
  (d : Array aspis_core.field.QM31 1024#usize)
  (g : Array aspis_core.field.QM31 1024#usize)
  (h1_padding : Array aspis_core.field.QM31 1024#usize) (commitments : T1)
  (hash : H) (variant : transport.Variant) :
  Safe (PV_L1D_Source_068.produce (H := H) (T1 := T1) aspis_coredigestDigest32Inst CommitmentsInst public1 compiled noised_semantic_c1 mask_only d g h1_padding commitments hash variant) := by
  unfold PV_L1D_Source_068.produce
  try simp only [PV_L1D_Projection.prod_case]
  repeat' first
    | solve | apply safe_PV_L1D_Source_067
    | solve | apply safe_PV_L1D_Source_039
    | exact safe_lift _
    | exact safe_coe _
    | exact safe_pure _
    | apply safe_observe; rfl
    | apply safe_bind
    | intro value
    | split <;> simp only [PV_L1D_Projection.prod_case]
#print axioms safe_PV_L1D_Source_068
theorem safe_PV_L1D_Source_069
  {T0 : Type} (aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst :
  aspis_prover.state_only_hiding.StateOnlyMaskNonceStore T0)
  (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (compiled :
  aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
  (variant : transport.Variant)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
  (binding : Array Std.U8 32#usize)
  (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets)
  (nonce_store : T0) :
  Safe (PV_L1D_Source_069.produce (T0 := T0) aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst public1 compiled variant hash context binding attempt nonce_store) := by
  unfold PV_L1D_Source_069.produce
  try simp only [PV_L1D_Projection.prod_case]
  repeat' first
    | solve | apply safe_PV_L1D_Source_068
    | solve | apply safe_PV_L1D_Source_038
    | solve | apply safe_PV_L1D_Source_037
    | solve | apply safe_PV_L1D_Source_031
    | solve | apply safe_PV_L1D_Source_030
    | exact safe_lift _
    | exact safe_coe _
    | exact safe_pure _
    | apply safe_observe; rfl
    | apply safe_bind
    | intro value
    | split <;> simp only [PV_L1D_Projection.prod_case]
#print axioms safe_PV_L1D_Source_069
theorem safe_PV_L1E_Source_070
  (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (compiled :
  aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
  (variant : transport.Variant)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets)
  (nonce_store :
  aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore) :
  Safe (PV_L1E_Source_070.produce public1 compiled variant hash attempt nonce_store) := by
  unfold PV_L1E_Source_070.produce
  try simp only [PV_L1D_Projection.prod_case]
  repeat' first
    | solve | apply safe_PV_L1D_Source_069
    | exact safe_lift _
    | exact safe_coe _
    | exact safe_pure _
    | apply safe_observe; rfl
    | apply safe_bind
    | intro value
    | split <;> simp only [PV_L1D_Projection.prod_case]
#print axioms safe_PV_L1E_Source_070
end PV_L1E_CallbackSafety
