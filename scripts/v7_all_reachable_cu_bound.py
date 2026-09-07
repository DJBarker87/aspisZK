#!/usr/bin/env python3
"""Fail-closed source inventory for the V7 terminal CU quantifier.

This tool does not pretend that sampled transactions prove a worst-case bound.
It checks the bounded-loop constants and the production-shaped rollover
withdrawal PDA call inventory against the source tree, then emits the exact
runtime-syscall floors that decide whether the current admission policy can
guarantee completion below Solana's transaction CU ceiling.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
RUNTIME_LIMIT = 1_400_000
MEASURED_ROLLOVER_C0_CU = 1_218_972
MEASURED_ROLLOVER_C0_FRONTIER = 202
CALIBRATED_CUTOFF20_MAX_FRONTIER_CU = 1_299_084
CUTOFF20_MAX_COUNTER = 20
MAX_FRONTIER_NODES = 203


def fail(message: str) -> None:
    raise SystemExit(f"FAIL: {message}")


def read(relative: str) -> str:
    path = ROOT / relative
    if not path.is_file():
        fail(f"missing source file: {relative}")
    return path.read_text(encoding="utf-8")


def require(pattern: str, text: str, description: str) -> None:
    if re.search(pattern, text, re.MULTILINE | re.DOTALL) is None:
        fail(f"source inventory mismatch: {description}")


def sha256(relative: str) -> str:
    return hashlib.sha256((ROOT / relative).read_bytes()).hexdigest()


def repository_revision() -> str:
    return subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args()

    transcript_path = "crates/aspis-core/src/transcript.rs"
    onefold_path = "crates/aspis-core/src/v7_onefold.rs"
    v6_transcript_path = "crates/aspis-core/src/v6_transcript.rs"
    state_only_sumcheck_path = "crates/aspis-core/src/state_only_sumcheck.rs"
    state_only_hiding_path = "crates/aspis-core/src/state_only_hiding.rs"
    prover_path = "crates/aspis-prover/src/v6_onefold_prover.rs"
    pool_path = "programs/aspis-pool/src/pair_forest.rs"
    pool_registry_path = "programs/aspis-pool/src/registry.rs"
    pool_nullifier_path = "programs/aspis-pool/src/nullifier.rs"
    pool_processor_path = "programs/aspis-pool/src/processor.rs"
    pool_vault_path = "programs/aspis-pool/src/vault.rs"
    verifier_dispatch_path = "programs/aspis-verifier/src/v7_pair_forest_dispatch.rs"

    transcript = read(transcript_path)
    onefold = read(onefold_path)
    v6_transcript = read(v6_transcript_path)
    state_only_sumcheck = read(state_only_sumcheck_path)
    state_only_hiding = read(state_only_hiding_path)
    prover = read(prover_path)
    pool = read(pool_path)
    pool_registry = read(pool_registry_path)
    pool_nullifier = read(pool_nullifier_path)
    pool_processor = read(pool_processor_path)
    pool_vault = read(pool_vault_path)
    verifier_dispatch = read(verifier_dispatch_path)

    require(r"CHALLENGE_RETRY_LIMIT:\s*u32\s*=\s*8", transcript, "QM31 retry limit")
    require(r"NONZERO_QM31_RETRY_LIMIT:\s*u32\s*=\s*3", transcript, "nonzero retry limit")
    require(r"CIRCLE_POINT_RETRY_LIMIT:\s*u32\s*=\s*3", transcript, "circle retry limit")
    require(r"challenge_queries_without_replacement\(V6_QUERY_COUNT,\s*1\s*<<\s*18,\s*64\)", onefold, "q16 draw limit")
    require(r"V7_COMPACT_QUERY_CANDIDATES:\s*usize\s*=\s*64", onefold, "candidate count")
    require(r"V7_COMPACT_FRONTIER_CAP_PER_TREE:\s*usize\s*=\s*203", onefold, "frontier cap")
    require(r"V7_FINAL_NONCE_COUNTER_CUTOFF:\s*u8\s*=\s*20", prover, "publication cutoff")
    require(r"challenge_queries\(V6_QUERY_COUNT,\s*1\s*<<\s*18\)", prover, "minimum-query-draw check")
    require(
        r"for index in 1\.\.Q\s*\{.*while cursor > 0 && value < queries\[cursor - 1\]",
        read("crates/aspis-core/src/v6_onefold.rs"),
        "candidate insertion-sort topology",
    )
    require(
        r"order\.sort_unstable_by_key\(\|entry\| entry\.0\)",
        onefold,
        "accepted-opening query sort",
    )

    # The accepted transcript has 30 direct QM31 calls, four nonzero samplers,
    # and two secure-circle samplers. Each successful QM31 call uses 1..4
    # squeeze blocks; nonzero/circle wrappers can each request 1..3 calls.
    direct_qm31 = 30
    nonzero_qm31 = 4
    secure_circle = 2
    minimum_qm31_calls = direct_qm31 + nonzero_qm31 + secure_circle
    maximum_qm31_calls = direct_qm31 + 3 * nonzero_qm31 + 3 * secure_circle
    minimum_qm31_squeeze_blocks = minimum_qm31_calls
    maximum_qm31_squeeze_blocks = maximum_qm31_calls * 4
    if (v6_transcript.count(".challenge_nonzero_qm31()")
            + state_only_hiding.count(".challenge_nonzero_qm31()")) < nonzero_qm31:
        fail("source inventory mismatch: nonzero challenge call inventory")
    require(r"for sample in 0\.\.2\s*\{.*challenge_secure_circle_point\(\)",
            v6_transcript, "two secure-circle challenge calls")
    require(r"STATE_ONLY_SUMCHECK_ROUNDS:\s*usize\s*=\s*10",
            state_only_sumcheck, "ten state-only sumcheck rounds")

    # Agave 4.2/4.3 execution-cost defaults. A 33-byte one-slice SHA-256 call
    # is 85 + max(10, floor(33/2)) = 101 CU. squeeze_block performs two calls.
    create_program_address_cu = 1_500
    sha256_base_cu = 85
    sha256_byte_cu = 1
    mem_op_base_cu = 10
    squeeze_hash_input_bytes = 33
    sha256_33_byte_cu = sha256_base_cu + max(
        mem_op_base_cu, sha256_byte_cu * (squeeze_hash_input_bytes // 2)
    )
    squeeze_block_syscall_cu = 2 * sha256_33_byte_cu
    maximum_additional_qm31_squeeze_syscall_cu = (
        maximum_qm31_squeeze_blocks - minimum_qm31_squeeze_blocks
    ) * squeeze_block_syscall_cu

    # Successful production-shaped rollover withdrawal call graph. Repeated
    # derivations are intentional: Pool and verifier independently authenticate
    # the same account identities. These are invocation counts, not unique PDAs.
    pda_calls = [
        ("pool.master decode", 1, pool_path, "pool_v1_pair_forest_master_address"),
        ("pool.checkpoint decode", 1, pool_path, "pool_v1_pair_forest_checkpoint_address"),
        ("pool.lane decode", 1, pool_path, "pool_v1_pair_forest_lane_address"),
        ("pool.request selected lane", 1, pool_path, "pool_v1_pair_forest_lane_address"),
        ("pool.current and rollover history pages", 2, pool_path, "require_root_page_address"),
        ("pool.nullifier marker initial plan", 1, pool_nullifier_path, "pool_v1_nullifier_marker_address"),
        ("pool.withdrawal vault authority and token PDA", 2, pool_vault_path, "pool_v1_vault_"),
        ("pool.nullifier marker post-create replan", 1, pool_processor_path, "plan_nullifier_marker_consumption_v1"),
        ("pool.Registry V2/programdata selection", 4, pool_registry_path, "find_program_address"),
        ("verifier.master/checkpoint/lane", 3, verifier_dispatch_path, "Pubkey::find_program_address"),
        ("verifier.Registry V2/programdata reauthentication", 4, verifier_dispatch_path, "Pubkey::find_program_address"),
    ]
    for label, count, path, needle in pda_calls:
        if read(path).count(needle) == 0:
            fail(f"PDA call inventory anchor missing: {label}")
        if count <= 0:
            fail(f"invalid PDA call inventory count: {label}")
    pda_invocations = sum(item[1] for item in pda_calls)
    if pda_invocations != 21:
        fail(f"expected 21 rollover-withdrawal PDA invocations, got {pda_invocations}")

    # Agave's on-chain syscall tries bumps 255 down through 1. A successful
    # derivation therefore uses 1..255 charged attempts. Exhausting all bumps
    # returns failure after a final (256th) charge and cannot reach a persisted
    # transition.
    pda_successful_attempts_per_invocation_max = 255
    pda_exhausted_failure_charges = 256
    pda_syscall_cu_per_successful_invocation_max = (
        pda_successful_attempts_per_invocation_max * create_program_address_cu
    )
    all_pda_syscall_cu_max = (
        pda_invocations * pda_syscall_cu_per_successful_invocation_max
    )
    one_maximal_pda_extra_cu_over_one_attempt = (
        (pda_successful_attempts_per_invocation_max - 1) * create_program_address_cu
    )

    # The cutoff policy fixes q16 to exactly two blocks per evaluated candidate,
    # but it does not constrain the QM31 wrappers or any PDA bump search.
    cutoff20_query_candidates_max = CUTOFF20_MAX_COUNTER + 1
    cutoff20_query_squeeze_blocks_max = cutoff20_query_candidates_max * 2
    verifier_language_query_squeeze_blocks_max = 64 * 8

    # binary_frontier_nodes insertion-sorts every 16-query candidate. Distinct
    # input order makes 15..120 comparisons reachable at the Rust level; the
    # cutoff policy constrains neither ordering nor the accepted-opening sort.
    q16_insertion_comparisons_min = 15
    q16_insertion_comparisons_max = 16 * 15 // 2

    single_maximal_pda_one_attempt_reference_envelope = (
        MEASURED_ROLLOVER_C0_CU + one_maximal_pda_extra_cu_over_one_attempt
    )
    all_maximal_pda_one_attempt_reference_envelope = (
        MEASURED_ROLLOVER_C0_CU
        + pda_invocations
        * (pda_successful_attempts_per_invocation_max - 1)
        * create_program_address_cu
    )

    source_files = sorted({
        transcript_path,
        onefold_path,
        "crates/aspis-core/src/v6_onefold.rs",
        v6_transcript_path,
        state_only_sumcheck_path,
        state_only_hiding_path,
        prover_path,
        pool_path,
        pool_registry_path,
        pool_nullifier_path,
        pool_processor_path,
        pool_vault_path,
        verifier_dispatch_path,
    })

    result = {
        "schema": "aspis.v7.all-reachable-cu-source-inventory.v1",
        "repositoryRevision": repository_revision(),
        "classification": "ALL-REACHABLE COMPLETION BOUND FAILS CLOSED",
        "quantifiers": {
            "verifierAcceptedLanguage": "counters 0..63; q16 draws up to 64 per candidate",
            "cutoff20PublishedSubset": "counters 0..20 and exactly 16 distinct initial q16 draws per evaluated candidate",
            "runtime": "Agave 4.2/4.3 default execution-cost schedule",
            "terminalShape": "fresh-marker withdrawal at a lane history-page rollover",
        },
        "limits": {
            "transactionCu": RUNTIME_LIMIT,
            "cutoff20InclusiveCounter": CUTOFF20_MAX_COUNTER,
            "frontierNodes": MAX_FRONTIER_NODES,
        },
        "measuredAnchor": {
            "transactionCu": MEASURED_ROLLOVER_C0_CU,
            "counter": 0,
            "frontierNodes": MEASURED_ROLLOVER_C0_FRONTIER,
            "qualification": "genuine strict-work LiteSVM rollover withdrawal; sample, not upper bound",
        },
        "calibratedCutoff20Envelope": {
            "transactionCu": CALIBRATED_CUTOFF20_MAX_FRONTIER_CU,
            "counter": CUTOFF20_MAX_COUNTER,
            "frontierNodes": MAX_FRONTIER_NODES,
            "runtimeHeadroomCu": RUNTIME_LIMIT - CALIBRATED_CUTOFF20_MAX_FRONTIER_CU,
            "additionalPdaAttemptsToCrossRuntimeLimit": (
                (RUNTIME_LIMIT - CALIBRATED_CUTOFF20_MAX_FRONTIER_CU)
                // create_program_address_cu
                + 1
            ),
            "qualification": (
                "two-comparison calibrated model with <=1 CU fit error; not an "
                "all-reachable upper bound"
            ),
        },
        "transcriptBoundedControlFlow": {
            "directQm31Calls": direct_qm31,
            "nonzeroQm31Wrappers": nonzero_qm31,
            "secureCircleWrappers": secure_circle,
            "minimumQm31Calls": minimum_qm31_calls,
            "maximumSuccessfulQm31Calls": maximum_qm31_calls,
            "squeezeBlocksPerSuccessfulQm31": {"minimum": 1, "maximum": 4},
            "minimumQm31SqueezeBlocks": minimum_qm31_squeeze_blocks,
            "maximumQm31SqueezeBlocks": maximum_qm31_squeeze_blocks,
            "maximumAdditionalQm31SqueezeBlocks": maximum_qm31_squeeze_blocks - minimum_qm31_squeeze_blocks,
            "sha256CuPer33ByteCall": sha256_33_byte_cu,
            "sha256SyscallCuPerSqueezeBlock": squeeze_block_syscall_cu,
            "maximumAdditionalQm31SqueezeSyscallCu": maximum_additional_qm31_squeeze_syscall_cu,
            "cutoff20QueryCandidatesMaximum": cutoff20_query_candidates_max,
            "cutoff20QuerySqueezeBlocksMaximum": cutoff20_query_squeeze_blocks_max,
            "verifierLanguageQuerySqueezeBlocksMaximum": verifier_language_query_squeeze_blocks_max,
            "cutoff20ConstrainsQm31Retries": False,
        },
        "queryOrderingBoundedControlFlow": {
            "queriesPerCandidate": 16,
            "binaryFrontierInsertionSortComparisons": {
                "minimum": q16_insertion_comparisons_min,
                "maximum": q16_insertion_comparisons_max,
            },
            "cutoff20MaximumCandidateComparisons": {
                "minimum": cutoff20_query_candidates_max * q16_insertion_comparisons_min,
                "maximum": cutoff20_query_candidates_max * q16_insertion_comparisons_max,
            },
            "acceptedOpeningSortElements": 16,
            "cutoff20ConstrainsQueryOrdering": False,
            "qualification": (
                "comparison count is source-bounded; no standalone SBF CU coefficient was "
                "inferred from the two-point calibrated envelope"
            ),
        },
        "combinedReferenceEnvelope": {
            "cutoff20MaxFrontierPlusMaximumSuccessfulQm31RetrySyscallCu": (
                CALIBRATED_CUTOFF20_MAX_FRONTIER_CU
                + maximum_additional_qm31_squeeze_syscall_cu
            ),
            "remainingRuntimeHeadroomCu": (
                RUNTIME_LIMIT
                - CALIBRATED_CUTOFF20_MAX_FRONTIER_CU
                - maximum_additional_qm31_squeeze_syscall_cu
            ),
            "additionalPdaAttemptsToCrossRuntimeLimit": (
                (
                    RUNTIME_LIMIT
                    - CALIBRATED_CUTOFF20_MAX_FRONTIER_CU
                    - maximum_additional_qm31_squeeze_syscall_cu
                )
                // create_program_address_cu
                + 1
            ),
            "qualification": (
                "additive source-cost comparison only; no claim that a joint SHA-256 "
                "preimage realizing every maximum has been constructed"
            ),
        },
        "pdaBoundedControlFlow": {
            "rolloverWithdrawalFindProgramAddressInvocations": pda_invocations,
            "inventory": [
                {"label": label, "invocations": count, "source": path, "anchor": needle}
                for label, count, path, needle in pda_calls
            ],
            "successfulAttemptsPerInvocation": {
                "minimum": 1,
                "maximum": pda_successful_attempts_per_invocation_max,
            },
            "exhaustedFailureChargesPerInvocation": pda_exhausted_failure_charges,
            "createProgramAddressCuPerAttempt": create_program_address_cu,
            "maximumSyscallCuPerSuccessfulInvocation": pda_syscall_cu_per_successful_invocation_max,
            "maximumSyscallCuAllInvocations": all_pda_syscall_cu_max,
            "oneMaximalInvocationExtraCuOverOneAttempt": one_maximal_pda_extra_cu_over_one_attempt,
            "oneAttemptReferenceEnvelopeWithOneMaximalInvocation": single_maximal_pda_one_attempt_reference_envelope,
            "oneAttemptReferenceEnvelopeWithAllMaximalInvocations": all_maximal_pda_one_attempt_reference_envelope,
            "referenceEnvelopeQualification": (
                "these values compare an otherwise identical one-attempt derivation with "
                "permitted maximal bump searches; they are not witnessed transactions and "
                "do not assert the measured fixture used one attempt"
            ),
            "cutoff20ConstrainsPdaAttempts": False,
        },
        "decision": {
            "cutoff20GuaranteesBelow1300000": False,
            "cutoff20GuaranteesBelow1400000": False,
            "verifierAcceptedLanguageGuaranteesBelow1400000": False,
            "reason": (
                "relative to an otherwise identical one-attempt derivation, one permitted "
                "255-attempt successful PDA search adds 381000 syscall CU, exceeding the measured "
                "rollover anchor's 181028-CU runtime headroom; the fixture's exact bump "
                "inventory is not encoded in the measurement, so the 1599972-CU value is "
                "a reference envelope rather than a witnessed transaction"
            ),
            "safeToPromoteAsUniversalCuPolicy": False,
            "byteIdenticalSimulationStillRequired": True,
        },
        "scope": {
            "productionSourceChanged": False,
            "verifierChanged": False,
            "proofFormatChanged": False,
            "relationChanged": False,
            "doesNotClaimJointSha256PreimageWitnessForEveryMaximalBranch": True,
            "doesProveCurrentAdmissionPolicyLeavesFiniteCostBranchesUngated": True,
        },
        "agaveCostScheduleProvenance": {
            "crateVersionInspected": "4.2.1",
            "executionBudgetSourceSha256": "139ecd8dd861bd8b82345d2d015702d6b25d5cb95e7d4fa9af06d678729d6e93",
            "syscallsSourceSha256": "e34a5bae92d7dde433a17ad61803894b7f501a8255484c9eee054710e6e61a9a",
            "successfulBumpRange": "255 down through 1",
        },
        "sourceSha256": {path: sha256(path) for path in source_files},
    }

    json.dump(result, sys.stdout, indent=2 if args.pretty else None, sort_keys=True)
    sys.stdout.write("\n")


if __name__ == "__main__":
    main()
