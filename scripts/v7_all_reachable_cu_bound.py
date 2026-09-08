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
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
EVIDENCE_ROOT = ROOT / "results/v7-all-reachable-cu-bound-pda-closure-20260908"
RUNTIME_LIMIT = 1_400_000
HISTORICAL_PROFILE_REVISION = 1
CURRENT_PROFILE_REVISION = 2
HISTORICAL_MEASURED_ROLLOVER_C0_CU = 1_218_972
HISTORICAL_MEASURED_ROLLOVER_C0_FRONTIER = 202
HISTORICAL_CALIBRATED_CUTOFF20_MAX_FRONTIER_CU = 1_299_084
CUTOFF20_MAX_COUNTER = 20
MAX_FRONTIER_NODES = 203
INVENTORY_START_REVISION = "e5640f79133f8afbeb7eb08a940abc6462274295"
DECODED_CHALLENGE_BINDING_REVISION = "8f36d51a173fcd513224c1ce6cd2cc2cc4e2901f"
CURRENT_SBF_SOURCE_REVISION = "acc4055b6c55ff6a568cf0d3d916365eccb4ebf1"
CURRENT_POOL_SBF_SHA256 = "cb5f90452ddd0772c5401f42ed0e28b7a38b7bb93ea0ac465cfab37fe7afd1a2"
CURRENT_VERIFIER_SBF_SHA256 = "8894c98c21583bdbd08f891367ece6fcb7570cbc53058250f4f87b5372260c66"
ROLLOVER_FULL_POOL_REFERENCE_CU = 119_206
ROLLOVER_ADDITIONAL_FIXED_PDA_CU = 1_500
ROLLOVER_ENVELOPE_CU = ROLLOVER_FULL_POOL_REFERENCE_CU + ROLLOVER_ADDITIONAL_FIXED_PDA_CU


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


def load_json(path: Path) -> dict:
    if not path.is_file():
        fail(f"missing evidence file: {path.relative_to(ROOT)}")
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        fail(f"invalid evidence JSON {path.relative_to(ROOT)}: {error}")
    if not isinstance(value, dict):
        fail(f"evidence root is not an object: {path.relative_to(ROOT)}")
    return value


def require_equal(actual: object, expected: object, description: str) -> None:
    if actual != expected:
        fail(f"evidence mismatch: {description}: expected {expected!r}, got {actual!r}")


def require_true(value: object, description: str) -> None:
    if value is not True:
        fail(f"evidence mismatch: {description} is not true")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args()

    transcript_path = "crates/aspis-core/src/transcript.rs"
    onefold_path = "crates/aspis-core/src/v7_onefold.rs"
    v6_onefold_path = "crates/aspis-core/src/v6_onefold.rs"
    compact_onefold_path = "crates/aspis-core/src/v7_compact_onefold.rs"
    fixed_canonical_path = "crates/aspis-core/src/v7_fixed_canonical_audit.rs"
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
    verifier_certificate_path = "programs/aspis-verifier/src/v7_terminal_pda_certificate.rs"
    cu_tail_probe_path = "programs/aspis-verifier/src/v7_cu_tail_probe.rs"

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
    compact_onefold = read(compact_onefold_path)
    fixed_canonical = read(fixed_canonical_path)
    verifier_certificate = read(verifier_certificate_path)
    cu_tail_probe = read(cu_tail_probe_path)

    require(r"CHALLENGE_RETRY_LIMIT:\s*u32\s*=\s*8", transcript, "QM31 retry limit")
    require(r"NONZERO_QM31_RETRY_LIMIT:\s*u32\s*=\s*3", transcript, "nonzero retry limit")
    require(r"CIRCLE_POINT_RETRY_LIMIT:\s*u32\s*=\s*3", transcript, "circle retry limit")
    require(r"V7_GAMMA_BIND_ID:\s*u8\s*=\s*0", transcript, "Tag-73 gamma bind id")
    require(r"V7_ALPHA_ZERO_BIND_ID:\s*u8\s*=\s*1", transcript, "Tag-73 alpha-zero bind id")
    require(r"V7_CHALLENGE_BIND:\s*u8\s*=\s*62", transcript, "Tag-73 causal-bind transcript label")
    require(
        r"fn bind_decoded_challenge\(.*let mut record = \[0u8; 17\];.*"
        r"record\[0\] = challenge_id;.*value\.write_le_bytes\(&mut record\[1\.\.\]\);.*"
        r"self\.absorb\(label::V7_CHALLENGE_BIND, &record\)",
        transcript,
        "Tag-73 decoded-value causal binding",
    )
    require(r"challenge_queries_without_replacement\(V6_QUERY_COUNT,\s*1\s*<<\s*18,\s*64\)", onefold, "q16 draw limit")
    require(r"V7_COMPACT_QUERY_CANDIDATES:\s*usize\s*=\s*64", onefold, "candidate count")
    require(r"V7_COMPACT_FRONTIER_CAP_PER_TREE:\s*usize\s*=\s*203", onefold, "frontier cap")
    require(r"V7_FINAL_NONCE_COUNTER_CUTOFF:\s*u8\s*=\s*20", prover, "publication cutoff")
    require(r"challenge_queries\(V6_QUERY_COUNT,\s*1\s*<<\s*18\)", prover, "minimum-query-draw check")
    require(
        r"OneFoldBuildProfile::V7Compact\s*=>\s*transcript\.challenge_nonzero_qm31_bound\(V7_GAMMA_BIND_ID\)",
        prover,
        "prover gamma causal binding",
    )
    require(
        r"OneFoldBuildProfile::V7Compact\s*=>\s*transcript\.challenge_qm31_bound\(V7_ALPHA_ZERO_BIND_ID\)",
        prover,
        "prover alpha-zero causal binding",
    )
    require(
        r"shift_query_batch_for_tag73\s*\{\s*transcript\.challenge_nonzero_qm31_bound\(V7_GAMMA_BIND_ID\)",
        v6_transcript,
        "verifier gamma causal binding",
    )
    require(
        r"shift_query_batch_for_tag73\s*\{\s*transcript\.challenge_qm31_bound\(V7_ALPHA_ZERO_BIND_ID\)",
        v6_transcript,
        "verifier alpha-zero causal binding",
    )
    require(
        r"0x81,\s*0x02,\s*8,\s*20,\s*18,\s*1,\s*64,\s*2",
        onefold,
        "causal-binding profile revision 2",
    )
    require(
        r"for index in 1\.\.Q\s*\{.*while cursor > 0 && value < queries\[cursor - 1\]",
        read(v6_onefold_path),
        "candidate insertion-sort topology",
    )
    require(
        r"fn sort_v7_query_order_source_bounded\(.*for index in 1\.\.V6_QUERY_COUNT.*"
        r"while cursor > 0 && value\.0 < order\[cursor - 1\]\.0",
        read(v6_onefold_path),
        "source-bounded accepted-opening query sort",
    )
    for selected_path, selected_source in (
        (onefold_path, onefold),
        (fixed_canonical_path, fixed_canonical),
        (compact_onefold_path, compact_onefold),
    ):
        require(
            r'cfg\(feature = "v7-query-order-source-bound-audit"\).*'
            r"sort_v7_query_order_source_bounded\(&mut order\).*"
            r'cfg\(not\(feature = "v7-query-order-source-bound-audit"\)\).*'
            r"sort_unstable_by_key",
            selected_source,
            f"selected/default-off opening sorter routing: {selected_path}",
        )
    require(
        r"if parameter\.c1 == crate::field::CM31::ZERO\s*\{\s*continue;\s*\}.*"
        r"secure_ood_circle_point_from_parameter\(parameter\)",
        transcript,
        "secure-circle subfield rejection before rational-map inversion",
    )
    require(
        r"V7_CU_TAIL_QM31_MIN_TAG:\s*u8\s*=\s*78.*"
        r"V7_CU_TAIL_QM31_MAX_TAG:\s*u8\s*=\s*79.*"
        r"V7_CU_TAIL_QUERY_ASCENDING_TAG:\s*u8\s*=\s*80.*"
        r"V7_CU_TAIL_QUERY_DESCENDING_TAG:\s*u8\s*=\s*81.*"
        r"V7_CU_TAIL_FRONTIER_14_TAG:\s*u8\s*=\s*86",
        cu_tail_probe,
        "isolated CU-tail probe wire tags",
    )
    require(
        r"fn real_hash_then_minimum_block\(.*crate::verify::sbf_hashv\(inputs\).*"
        r"fn controlled_maximum_block\(.*crate::verify::sbf_hashv\(inputs\).*"
        r"for word in block\.chunks_exact_mut\(4\)\.take\(7\).*"
        r"P\.to_le_bytes\(\)",
        cu_tail_probe,
        "CU-tail probe executes real SHA before controlled successful outputs",
    )
    require(
        r"for _ in 0\.\.30\s*\{.*challenge_qm31\(\).*"
        r"for _ in 0\.\.4\s*\{.*challenge_nonzero_qm31\(\).*"
        r"for _ in 0\.\.2\s*\{.*challenge_secure_circle_point\(\)",
        cu_tail_probe,
        "CU-tail probe exact accepted challenge topology",
    )
    require(
        r"for candidate in 0\.\.21u32\s*\{.*binary_frontier_nodes\(queries, 18\).*"
        r"sort_v7_query_order_source_bounded\(&mut order\)",
        cu_tail_probe,
        "CU-tail probe cutoff-20 candidate and opening ordering topology",
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
    minimum_qm31_word_attempts = minimum_qm31_calls * 4
    maximum_qm31_word_attempts = maximum_qm31_calls * 4 * 8
    maximum_outer_nonzero_rejections = nonzero_qm31 * 2
    maximum_outer_circle_rejections = secure_circle * 2
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

    # Revision 2 immediately absorbs two canonical decoded-value records.
    # `absorb` packs state (32), domain+label (2), and the 17-byte record into
    # one 51-byte slice. Agave charges the base once plus
    # max(mem_op_base, floor(total_bytes/2)), so each bind syscall is 110 CU
    # and the two-call fixed floor is 220 CU. This is not a complete SBF
    # measurement: the packing/copy/instruction overhead must be measured in
    # the current binary.
    causal_bind_calls = 2
    causal_bind_slice_bytes = [32 + 2 + 17]
    causal_bind_input_bytes = sum(causal_bind_slice_bytes)
    causal_bind_sha256_cu_per_call = sha256_base_cu + sum(
        max(mem_op_base_cu, sha256_byte_cu * (length // 2))
        for length in causal_bind_slice_bytes
    )
    causal_bind_sha256_cu_total = causal_bind_calls * causal_bind_sha256_cu_per_call

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

    # Agave's canonical search tries every bump from 255 down through zero.
    # A bump-zero success therefore uses all 256 charged attempts.
    pda_successful_attempts_per_invocation_max = 256
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

    # The APD8 proof-preparation certificate runs those canonical searches
    # before the terminal transaction. Its verifier-owned immutable bytes are
    # replayed with fixed create_program_address attempts in the terminal.
    require(r"fn require_canonical_bumps\(.*find_program_address", verifier_certificate,
            "certificate-time canonical bump search")
    require(r"fn require_created_address\(.*create_program_address", verifier_certificate,
            "certificate terminal single-attempt replay")
    require(r"destination\.copy_from_slice", verifier_certificate,
            "immutable certificate initialization write")
    terminal_find_program_address_after = 0
    terminal_single_attempts = {
        "samePageTransfer": 11,
        "rolloverTransfer": 12,
        "samePageWithdrawal": 15,
        "rolloverWithdrawal": 16,
    }
    maximum_terminal_single_attempts = max(terminal_single_attempts.values())
    maximum_terminal_pda_syscall_cu = maximum_terminal_single_attempts * create_program_address_cu

    # The cutoff policy fixes q16 to exactly two blocks per evaluated candidate,
    # but it does not constrain the QM31 wrappers or any PDA bump search.
    cutoff20_query_candidates_max = CUTOFF20_MAX_COUNTER + 1
    cutoff20_query_squeeze_blocks_max = cutoff20_query_candidates_max * 2
    verifier_language_query_squeeze_blocks_max = 64 * 8

    # binary_frontier_nodes insertion-sorts every 16-query candidate. Distinct
    # input order makes 15..120 comparisons reachable at the Rust level. The
    # audit opening consumer uses the same explicit source-visible topology.
    q16_insertion_comparisons_min = 15
    q16_insertion_comparisons_max = 16 * 15 // 2
    cutoff20_query_comparisons_min = cutoff20_query_candidates_max * q16_insertion_comparisons_min
    cutoff20_query_comparisons_max = cutoff20_query_candidates_max * q16_insertion_comparisons_max
    opening_query_comparisons_min = q16_insertion_comparisons_min
    opening_query_comparisons_max = q16_insertion_comparisons_max

    historical_single_maximal_pda_one_attempt_reference_envelope = (
        HISTORICAL_MEASURED_ROLLOVER_C0_CU + one_maximal_pda_extra_cu_over_one_attempt
    )
    historical_all_maximal_pda_one_attempt_reference_envelope = (
        HISTORICAL_MEASURED_ROLLOVER_C0_CU
        + pda_invocations
        * (pda_successful_attempts_per_invocation_max - 1)
        * create_program_address_cu
    )

    source_files = sorted({
        transcript_path,
        onefold_path,
        v6_onefold_path,
        compact_onefold_path,
        fixed_canonical_path,
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
        verifier_certificate_path,
        cu_tail_probe_path,
    })

    # Freeze current-binary evidence and recompute every delta used below.
    tail_path = EVIDENCE_ROOT / "cu-tail-probe/summary.json"
    tail = load_json(tail_path)
    require_equal(tail.get("schema"), "aspis.v7.cu-tail-probe-evidence.v1", "tail schema")
    require_true(tail.get("localOnly"), "tail probe local-only classification")
    require_equal(tail.get("probeBinarySha256"),
                  "f71713a8c50bdb62111012856332a364f7800a68e604e6d6de0ed343f812ec04",
                  "tail probe binary hash")
    require_equal(tail.get("publicClusterTransaction"), False, "tail probe public-cluster flag")
    require_equal(tail.get("mainnetReady"), False, "tail probe mainnet flag")
    tail_cases = {case.get("name"): case for case in tail.get("cases", [])}
    expected_tail_names = {
        "qm31-minimum", "qm31-maximum-successful", "query-order-best", "query-order-worst",
        "counter-zero", "counter-twenty", "frontier-14", "frontier-199", "frontier-203",
    }
    require_equal(set(tail_cases), expected_tail_names, "tail case names")
    for name, case in tail_cases.items():
        require_true(case.get("simulationSubmissionWireIdentical"), f"{name} byte identity")
        require_equal(case.get("simulationCu"), case.get("landedCu"), f"{name} simulation/landed CU")
        if not isinstance(case.get("finalizedSlot"), int) or case["finalizedSlot"] <= 0:
            fail(f"evidence mismatch: {name} did not finalize")
        if not isinstance(case.get("signedWireSha256"), str) or len(case["signedWireSha256"]) != 64:
            fail(f"evidence mismatch: {name} signed wire hash")
    tail_deltas = {
        "qm31MaximumMinusMinimum": (
            tail_cases["qm31-maximum-successful"]["landedCu"]
            - tail_cases["qm31-minimum"]["landedCu"]
        ),
        "queryWorstMinusBest": (
            tail_cases["query-order-worst"]["landedCu"]
            - tail_cases["query-order-best"]["landedCu"]
        ),
        "counterTwentyMinusZero": (
            tail_cases["counter-twenty"]["landedCu"]
            - tail_cases["counter-zero"]["landedCu"]
        ),
        "frontier203Minus199": (
            tail_cases["frontier-203"]["landedCu"]
            - tail_cases["frontier-199"]["landedCu"]
        ),
        "frontier203Minus14": (
            tail_cases["frontier-203"]["landedCu"]
            - tail_cases["frontier-14"]["landedCu"]
        ),
    }
    require_equal(tail.get("landedDeltasCu"), tail_deltas, "recomputed tail deltas")

    def validate_terminal(kind: str, fixed_pda_attempts: int) -> tuple[dict, dict, dict]:
        base = EVIDENCE_ROOT / f"current-{kind}-selected-sort"
        terminal = load_json(base / "terminal/terminal-finalized.json")
        signed = load_json(base / "terminal/signed-request.json")
        proof_wrapper = load_json(base / "proof/genuine-live-proof.json")
        closure = load_json(base / "closure/proof-close-finalized.json")
        cluster = load_json(base / "cluster/cluster.json")
        operation = "withdrawal" if kind == "withdrawal" else "transfer"
        require_equal(terminal.get("schema"), "aspis.v7.live-terminal-finalized.v1",
                      f"{kind} terminal schema")
        require_equal(terminal.get("operation"), operation, f"{kind} operation")
        require_true(terminal.get("finalized"), f"{kind} finalized")
        require_true(terminal.get("byteIdenticalSimulationSubmission"), f"{kind} byte identity")
        require_equal(terminal.get("simulatedCu"), terminal.get("landedCu"),
                      f"{kind} simulation/landed CU")
        require_equal(terminal.get("terminalInstructionCount"), 1, f"{kind} terminal count")
        require_true(terminal.get("ciphertextCarrierRealHpke"), f"{kind} real HPKE carrier")
        require_true(terminal.get("ciphertextCarrierCanonical"), f"{kind} canonical carrier")
        require_equal(terminal.get("carrierTestMode"), None, f"{kind} carrier test mode")
        require_true(terminal.get("auditOnly"), f"{kind} audit-only identity")
        require_true(terminal.get("disposable"), f"{kind} disposable classification")
        require_equal(terminal.get("publicDevnetTestOnly"), False, f"{kind} public Devnet flag")
        require_equal(terminal.get("mainnetReady"), False, f"{kind} mainnet flag")
        if terminal.get("serializedTransactionBytes", 4096) >= 4096:
            fail(f"evidence mismatch: {kind} transaction is not below 4096 bytes")
        require_true(signed.get("terminalPdaClosureEnabled"), f"{kind} PDA closure")
        pda = signed.get("pdaSearchAudit", {})
        require_equal(pda.get("terminalVariableFindProgramAddressInvocations"), 0,
                      f"{kind} terminal variable PDA calls")
        require_equal(pda.get("terminalSingleAttemptValidations"), fixed_pda_attempts,
                      f"{kind} fixed PDA attempts")
        require_equal(pda.get("terminalPdaSyscallTheoreticalMaximumCu"),
                      fixed_pda_attempts * create_program_address_cu,
                      f"{kind} fixed PDA CU")
        require_equal(signed.get("signedWireSha256"), terminal.get("signedWireSha256"),
                      f"{kind} signed wire hash")
        require_equal(hashlib.sha256((base / "terminal/accounts-before.json").read_bytes()).hexdigest(),
                      terminal.get("protectedAccountsBeforeJsonSha256"),
                      f"{kind} protected before-account hash")
        require_equal(hashlib.sha256((base / "terminal/accounts-after.json").read_bytes()).hexdigest(),
                      terminal.get("protectedAccountsAfterJsonSha256"),
                      f"{kind} protected after-account hash")
        proof = proof_wrapper.get("proof", {})
        require_equal(proof.get("operation"), operation, f"{kind} proof operation")
        require_equal(proof.get("deterministicFixtureEntropy"), False, f"{kind} fixture entropy")
        require_equal(proof.get("trustedResultAccount"), False, f"{kind} trusted result")
        require_equal(proof.get("verifierBypass"), False, f"{kind} verifier bypass")
        selection = proof.get("finalNonceSelection", {})
        require_true(selection.get("enabled"), f"{kind} cutoff selection")
        require_equal(selection.get("maxCompactCounter"), CUTOFF20_MAX_COUNTER,
                      f"{kind} cutoff")
        require_true(selection.get("minimumQueryDrawsPerEvaluatedCandidateRequired"),
                     f"{kind} minimum q16 draws")
        counter = selection.get("selectedCounter")
        if not isinstance(counter, int) or not 0 <= counter <= CUTOFF20_MAX_COUNTER:
            fail(f"evidence mismatch: {kind} counter outside cutoff-20")
        require_true(proof.get("proof", {}).get("powValid"), f"{kind} proof work")
        require_true(closure.get("finalized"), f"{kind} proof close finalized")
        require_true(closure.get("byteIdenticalSimulationSubmission"), f"{kind} close byte identity")
        require_true(closure.get("proofAccountDrained"), f"{kind} proof account drained")
        require_equal(cluster.get("agave", {}).get("coreVersion"), "4.2.2", f"{kind} Agave")
        require_true(cluster.get("cluster", {}).get("feature", {}).get("active"),
                     f"{kind} TxV1 feature")
        require_equal(cluster.get("cluster", {}).get("feature", {}).get("activationSlot"), 0,
                      f"{kind} TxV1 genesis activation")
        programs = {item.get("name"): item for item in cluster.get("identities", {}).get("configuredPrograms", [])}
        require_equal(programs.get("pool", {}).get("sha256"), CURRENT_POOL_SBF_SHA256,
                      f"{kind} Pool SBF")
        require_equal(programs.get("verifier", {}).get("sha256"), CURRENT_VERIFIER_SBF_SHA256,
                      f"{kind} verifier SBF")
        require_equal(cluster.get("repository", {}).get("revision"), CURRENT_SBF_SOURCE_REVISION,
                      f"{kind} SBF source revision")
        if operation == "withdrawal":
            custody = terminal.get("custody", {})
            require_true(custody.get("conservation"), "withdrawal custody conservation")
            require_true(custody.get("destinationBinding"), "withdrawal destination binding")
        return terminal, proof, signed

    transfer_terminal, transfer_proof, transfer_signed = validate_terminal("transfer", 11)
    withdrawal_terminal, withdrawal_proof, withdrawal_signed = validate_terminal("withdrawal", 15)

    # The terminal rollover branch has one extra pre-created zeroed history
    # page and one additional fixed-bump validation.  Conservatively add the
    # entire measured production-shaped rollover Pool transaction (not merely
    # its same/rollover delta) plus that fixed 1,500-CU PDA attempt.  The old
    # measurement used a transport-only verifier; it is therefore never used
    # as a combined verifier measurement.  Adding its complete Pool cost to a
    # genuine current combined same-page transaction deliberately double-counts
    # the common Pool prefix, verifier transport, marker and state writes.
    rollover_reference_path = ROOT / "results/pool-v1-pair-afterstate-litesvm-20260827/evidence-rollover.json"
    rollover_reference = load_json(rollover_reference_path)
    require_equal(rollover_reference.get("schema"),
                  "aspis.pool-v1.pair-afterstate-runtime-evidence.v1", "rollover reference schema")
    require_equal(rollover_reference.get("mode"), "rollover", "rollover reference mode")
    require_equal(rollover_reference.get("execution", {}).get("compute_units"),
                  ROLLOVER_FULL_POOL_REFERENCE_CU, "rollover full Pool CU")
    require_true(rollover_reference.get("execution", {}).get("simulation_equals_execution"),
                 "rollover reference simulation/execution equality")
    require_true(rollover_reference.get("state_transition", {}).get("full_prior_page_byte_exact_on_rollover"),
                 "rollover prior-page preservation")

    full_tail_envelope_cu = (
        tail_deltas["counterTwentyMinusZero"]
        + tail_deltas["frontier203Minus14"]
        + tail_deltas["qm31MaximumMinusMinimum"]
        + tail_deltas["queryWorstMinusBest"]
    )
    transfer_same_ceiling = transfer_terminal["landedCu"] + full_tail_envelope_cu
    transfer_rollover_ceiling = transfer_same_ceiling + ROLLOVER_ENVELOPE_CU
    withdrawal_same_ceiling = withdrawal_terminal["landedCu"] + full_tail_envelope_cu
    withdrawal_rollover_ceiling = withdrawal_same_ceiling + ROLLOVER_ENVELOPE_CU
    shape_ceilings = {
        "samePageTransfer": transfer_same_ceiling,
        "rolloverTransfer": transfer_rollover_ceiling,
        "samePageWithdrawal": withdrawal_same_ceiling,
        "rolloverWithdrawal": withdrawal_rollover_ceiling,
    }
    universal_ceiling = max(shape_ceilings.values())
    if universal_ceiling >= RUNTIME_LIMIT:
        fail(f"computed all-reachable ceiling {universal_ceiling} is not below {RUNTIME_LIMIT}")
    release_classification = (
        "B — RELEASE-MARGIN GREEN" if universal_ceiling <= 1_350_000
        else "A — ALL-REACHABLE GREEN"
    )

    result = {
        "schema": "aspis.v7.all-reachable-cu-source-inventory.v4",
        "inventoryStartRevision": INVENTORY_START_REVISION,
        "decodedChallengeBindingRevision": DECODED_CHALLENGE_BINDING_REVISION,
        "revisionQualification": (
            "source hashes below pin the exact audited files; the start revision records the "
            "containing tree before this inventory repair"
        ),
        "classification": "PDA TAIL CLOSED; CURRENT-BINARY MEASUREMENT AND RESIDUAL SBF COEFFICIENTS MISSING",
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
        "currentProfile": {
            "revision": CURRENT_PROFILE_REVISION,
            "productionSbfMeasurements": {
                "publicDevnetSamePageTransferCu": 1_154_057,
                "publicDevnetSamePageWithdrawalCu": 1_177_631,
                "verifierBinarySha256": "5476d70d03fc3e55cee7bd3d7747023195713d0639afd9be66908e7ce09430c3",
                "poolBinarySha256": "9cd1401327493134ca42ed13a7e72d7e6c375c488f7aa2ede42b39f402b6c89d",
                "evidence": "results/v7-txv1-public-devnet-identity-fix-20260907/public-devnet-summary.json",
            },
            "cutoff20Frontier203Measurement": None,
            "samePageMeasurementAvailable": True,
            "requiredRolloverBoundFixtureAvailable": False,
            "reason": (
                "current profile production binaries and honest same-page proofs were measured "
                "on public Devnet, but no current-binary counter-20/frontier-203 rollover fixture exists"
            ),
        },
        "historicalMeasuredAnchor": {
            "profileRevision": HISTORICAL_PROFILE_REVISION,
            "currentProfileApplicable": False,
            "transactionCu": HISTORICAL_MEASURED_ROLLOVER_C0_CU,
            "counter": 0,
            "frontierNodes": HISTORICAL_MEASURED_ROLLOVER_C0_FRONTIER,
            "qualification": (
                "genuine strict-work LiteSVM rollover withdrawal for profile revision 1; "
                "sample, not an upper bound and not a revision-2 measurement"
            ),
        },
        "historicalCalibratedCutoff20Envelope": {
            "profileRevision": HISTORICAL_PROFILE_REVISION,
            "currentProfileApplicable": False,
            "transactionCu": HISTORICAL_CALIBRATED_CUTOFF20_MAX_FRONTIER_CU,
            "counter": CUTOFF20_MAX_COUNTER,
            "frontierNodes": MAX_FRONTIER_NODES,
            "runtimeHeadroomCu": RUNTIME_LIMIT - HISTORICAL_CALIBRATED_CUTOFF20_MAX_FRONTIER_CU,
            "additionalPdaAttemptsToCrossRuntimeLimit": (
                (RUNTIME_LIMIT - HISTORICAL_CALIBRATED_CUTOFF20_MAX_FRONTIER_CU)
                // create_program_address_cu
                + 1
            ),
            "qualification": (
                "revision-1 two-comparison calibrated model with <=1 CU fit error; "
                "not an all-reachable bound and not applicable to revision 2"
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
            "minimumQm31WordAttempts": minimum_qm31_word_attempts,
            "maximumQm31WordAttempts": maximum_qm31_word_attempts,
            "maximumAdditionalQm31WordAttempts": maximum_qm31_word_attempts - minimum_qm31_word_attempts,
            "maximumOuterNonzeroRejections": maximum_outer_nonzero_rejections,
            "maximumOuterCircleRejections": maximum_outer_circle_rejections,
            "variableRejectedCircleInversionsAfterPrecheck": 0,
            "successfulCircleRationalMaps": secure_circle,
            "sha256CuPer33ByteCall": sha256_33_byte_cu,
            "sha256SyscallCuPerSqueezeBlock": squeeze_block_syscall_cu,
            "maximumAdditionalQm31SqueezeSyscallCu": maximum_additional_qm31_squeeze_syscall_cu,
            "cutoff20QueryCandidatesMaximum": cutoff20_query_candidates_max,
            "cutoff20QuerySqueezeBlocksMaximum": cutoff20_query_squeeze_blocks_max,
            "verifierLanguageQuerySqueezeBlocksMaximum": verifier_language_query_squeeze_blocks_max,
            "cutoff20ConstrainsQm31Retries": False,
        },
        "causalChallengeBindingRevision2": {
            "profileRevision": CURRENT_PROFILE_REVISION,
            "bindCalls": causal_bind_calls,
            "sha256SlicesPerCall": causal_bind_slice_bytes,
            "inputBytesPerCall": causal_bind_input_bytes,
            "sha256SyscallCuPerCall": causal_bind_sha256_cu_per_call,
            "fixedSha256SyscallCu": causal_bind_sha256_cu_total,
            "canonicalDecodedRecordBytes": 17,
            "packedAbsorbBytes": 51,
            "sbfCopyAndLoopOverheadMeasured": False,
            "qualification": (
                "220 CU is the exact Agave SHA-256 syscall charge only; it must not "
                "be treated as the complete revision-2 binary delta"
            ),
        },
        "queryOrderingBoundedControlFlow": {
            "queriesPerCandidate": 16,
            "binaryFrontierInsertionSortComparisons": {
                "minimum": q16_insertion_comparisons_min,
                "maximum": q16_insertion_comparisons_max,
            },
            "cutoff20MaximumCandidateComparisons": {
                "minimum": cutoff20_query_comparisons_min,
                "maximum": cutoff20_query_comparisons_max,
            },
            "acceptedOpeningSortElements": 16,
            "acceptedOpeningInsertionSortComparisons": {
                "minimum": opening_query_comparisons_min,
                "maximum": opening_query_comparisons_max,
            },
            "totalCutoff20AndOpeningComparisons": {
                "minimum": cutoff20_query_comparisons_min + opening_query_comparisons_min,
                "maximum": cutoff20_query_comparisons_max + opening_query_comparisons_max,
            },
            "sourceBoundedOpeningFeature": "v7-query-order-source-bound-audit",
            "cutoff20ConstrainsQueryOrdering": False,
            "qualification": (
                "candidate and opening comparison counts are source-bounded; no standalone "
                "current-SBF CU coefficient is inferred without the required capped build"
            ),
        },
        "disposableCuTailProbe": {
            "feature": "v7-cu-probe",
            "entrypointProductionReachable": False,
            "qm31Cases": ["minimum", "maximum-successful"],
            "queryOrderCases": ["best", "worst"],
            "realShaSyscallExecutedBeforeControlledBlock": True,
            "signedWireBuilder": "tools/v7-live-pool-proof/src/bin/build_v7_cu_tail_probe.rs",
            "byteIdenticalFinalizedRunner": "scripts/v7_cu_tail_probe_child.sh",
            "currentSbfMeasurementAvailable": False,
            "blockedBy": "dedicated Linux build host offline; Tailscale node key expired",
        },
        "historicalCombinedReferenceEnvelope": {
            "profileRevision": HISTORICAL_PROFILE_REVISION,
            "currentProfileApplicable": False,
            "cutoff20MaxFrontierPlusMaximumSuccessfulQm31RetrySyscallCu": (
                HISTORICAL_CALIBRATED_CUTOFF20_MAX_FRONTIER_CU
                + maximum_additional_qm31_squeeze_syscall_cu
            ),
            "remainingRuntimeHeadroomCu": (
                RUNTIME_LIMIT
                - HISTORICAL_CALIBRATED_CUTOFF20_MAX_FRONTIER_CU
                - maximum_additional_qm31_squeeze_syscall_cu
            ),
            "additionalPdaAttemptsToCrossRuntimeLimit": (
                (
                    RUNTIME_LIMIT
                    - HISTORICAL_CALIBRATED_CUTOFF20_MAX_FRONTIER_CU
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
            "historicalProfileRevision": HISTORICAL_PROFILE_REVISION,
            "currentProfileApplicable": False,
            "oneAttemptReferenceEnvelopeWithOneMaximalInvocation": historical_single_maximal_pda_one_attempt_reference_envelope,
            "oneAttemptReferenceEnvelopeWithAllMaximalInvocations": historical_all_maximal_pda_one_attempt_reference_envelope,
            "referenceEnvelopeQualification": (
                "these values compare an otherwise identical one-attempt derivation with "
                "permitted maximal bump searches; they are not witnessed transactions and "
                "do not assert the measured fixture used one attempt"
            ),
            "cutoff20ConstrainsPdaAttempts": False,
            "authenticatedTerminalClosure": {
                "feature": "v7-terminal-pda-certificate-audit",
                "canonicalSearchLocation": "sealed-proof preparation transaction",
                "certificateOwner": "selected verifier program",
                "terminalFindProgramAddressInvocations": terminal_find_program_address_after,
                "terminalSingleAttemptValidations": terminal_single_attempts,
                "maximumTerminalSingleAttempts": maximum_terminal_single_attempts,
                "maximumTerminalPdaSyscallCu": maximum_terminal_pda_syscall_cu,
                "variablePdaTailClosed": True,
                "terminalWireByteDelta": 33,
            },
        },
        "decision": {
            "cutoff20GuaranteesBelow1300000": False,
            "cutoff20GuaranteesBelow1400000": False,
            "verifierAcceptedLanguageGuaranteesBelow1400000": False,
            "reason": (
                "the PDA search tail is closed behind the default-off certificate, but no "
                "certificate-enabled current-binary counter-20/frontier-203 rollover measurement "
                "or exact SBF coefficient for bounded QM31 CPU/query-order work exists yet"
            ),
            "safeToPromoteAsUniversalCuPolicy": False,
            "byteIdenticalSimulationStillRequired": True,
        },
        "scope": {
            "productionSourceChanged": True,
            "verifierChanged": True,
            "proofFormatChanged": False,
            "relationChanged": False,
            "acceptedTranscriptProfileChangedSinceHistoricalMeasurements": True,
            "doesNotClaimJointSha256PreimageWitnessForEveryMaximalBranch": True,
            "doesProveCurrentAdmissionPolicyLeavesFiniteCostBranchesUngated": True,
        },
        "agaveCostScheduleProvenance": {
            "crateVersionInspected": "4.2.1",
            "executionBudgetSourceSha256": "139ecd8dd861bd8b82345d2d015702d6b25d5cb95e7d4fa9af06d678729d6e93",
            "syscallsSourceSha256": "e34a5bae92d7dde433a17ad61803894b7f501a8255484c9eee054710e6e61a9a",
            "successfulBumpRange": "255 down through 0",
        },
        "sourceSha256": {path: sha256(path) for path in source_files},
    }

    # Replace the pre-measurement classification with the fail-closed current
    # evidence result.  Historical fields remain above for provenance only.
    result.update({
        "schema": "aspis.v7.all-reachable-cu-bound.v5",
        "classification": release_classification,
        "currentSbfSourceRevision": CURRENT_SBF_SOURCE_REVISION,
        "currentSbf": {
            "agaveVersion": "4.2.2",
            "poolSha256": CURRENT_POOL_SBF_SHA256,
            "verifierSha256": CURRENT_VERIFIER_SBF_SHA256,
            "proofFormatChanged": False,
            "relationChanged": False,
        },
        "currentProfile": {
            "revision": CURRENT_PROFILE_REVISION,
            "genuineFinalizedSamePage": {
                "transfer": {
                    "cu": transfer_terminal["landedCu"],
                    "verifierCpiCu": 1_000_153,
                    "bytes": transfer_terminal["serializedTransactionBytes"],
                    "counter": transfer_proof["proof"]["compactCounter"],
                    "frontierNodes": transfer_proof["proof"]["frontierNodes"],
                    "signature": transfer_terminal["signature"],
                    "slot": transfer_terminal["slot"],
                    "wireSha256": transfer_terminal["signedWireSha256"],
                    "beforeAccountsSha256": transfer_terminal["protectedAccountsBeforeJsonSha256"],
                    "afterAccountsSha256": transfer_terminal["protectedAccountsAfterJsonSha256"],
                    "proofSha256": transfer_proof["proof"]["sha256"],
                },
                "withdrawal": {
                    "cu": withdrawal_terminal["landedCu"],
                    "verifierCpiCu": 976_371,
                    "bytes": withdrawal_terminal["serializedTransactionBytes"],
                    "counter": withdrawal_proof["proof"]["compactCounter"],
                    "frontierNodes": withdrawal_proof["proof"]["frontierNodes"],
                    "signature": withdrawal_terminal["signature"],
                    "slot": withdrawal_terminal["slot"],
                    "wireSha256": withdrawal_terminal["signedWireSha256"],
                    "beforeAccountsSha256": withdrawal_terminal["protectedAccountsBeforeJsonSha256"],
                    "afterAccountsSha256": withdrawal_terminal["protectedAccountsAfterJsonSha256"],
                    "proofSha256": withdrawal_proof["proof"]["sha256"],
                },
            },
            "directCurrentRolloverMeasurementAvailable": False,
            "rolloverQualification": (
                "bounded from the exact current fixed-shape branch by conservatively adding an "
                "entire production-shaped rollover Pool transaction plus its one additional "
                "fixed PDA attempt to each genuine current same-page combined anchor"
            ),
        },
        "measuredTailDeltasCu": tail_deltas,
        "allReachableArithmetic": {
            "method": (
                "for each genuine current combined anchor, add every full independently measured "
                "successful-path tail range, even though the anchor already lies inside each range; "
                "for rollover also add the complete prior production-shaped rollover Pool cost and "
                "the current extra fixed PDA attempt"
            ),
            "commonTailEnvelopeCu": {
                "cutoff20CounterFullRange": tail_deltas["counterTwentyMinusZero"],
                "frontier14To203FullGrammarRange": tail_deltas["frontier203Minus14"],
                "frontier199To203DiagnosticRange": tail_deltas["frontier203Minus199"],
                "qm31MinimumToMaximumSuccessfulFullTopology": tail_deltas["qm31MaximumMinusMinimum"],
                "queryOrderingBestToWorstAllCandidatesAndOpening": tail_deltas["queryWorstMinusBest"],
                "total": full_tail_envelope_cu,
            },
            "rolloverEnvelopeCu": {
                "completeProductionShapedPoolRolloverReference": ROLLOVER_FULL_POOL_REFERENCE_CU,
                "additionalCurrentFixedPdaAttempt": ROLLOVER_ADDITIONAL_FIXED_PDA_CU,
                "total": ROLLOVER_ENVELOPE_CU,
                "deliberatelyDoubleCountsCommonPoolWork": True,
                "systemAccountCreationInTerminal": False,
                "nextHistoryPageMustBePrecreatedZeroedPoolOwned": True,
            },
            "shapeCeilingsCu": shape_ceilings,
            "maximumShape": max(shape_ceilings, key=shape_ceilings.get),
            "universalCeilingCu": universal_ceiling,
            "marginTo1400000Cu": RUNTIME_LIMIT - universal_ceiling,
            "marginTo1350000Cu": 1_350_000 - universal_ceiling,
            "marginTo1300000Cu": 1_300_000 - universal_ceiling,
        },
        "residualRuntimeTails": {
            "pdaSearch": "closed: zero terminal find_program_address calls",
            "qm31SuccessfulRetries": "bounded by source loop limits and full accepted-topology SBF delta",
            "queryOrdering": "bounded by source-visible insertion loops and full cutoff-20 plus opening SBF delta",
            "q16Counter": "bounded by cutoff-20 publication bridge and full counter-0-to-20 SBF delta",
            "frontier": "bounded by the 203-node grammar cap and full 199-to-203 SBF delta",
            "uncontrolledAcceptedBranches": [],
        },
        "evidence": {
            "tailProbe": str(tail_path.relative_to(ROOT)),
            "transfer": str((EVIDENCE_ROOT / "current-transfer-selected-sort").relative_to(ROOT)),
            "withdrawal": str((EVIDENCE_ROOT / "current-withdrawal-selected-sort").relative_to(ROOT)),
            "rolloverReference": str(rollover_reference_path.relative_to(ROOT)),
            "formal": str((EVIDENCE_ROOT / "formal").relative_to(ROOT)),
            "terminalPdaInventory": str((EVIDENCE_ROOT / "source-inventory/terminal-pda-inventory.json").relative_to(ROOT)),
        },
        "decision": {
            "cutoff20GuaranteesBelow1300000": universal_ceiling <= 1_300_000,
            "cutoff20GuaranteesBelow1350000": universal_ceiling <= 1_350_000,
            "cutoff20GuaranteesBelow1400000": universal_ceiling < RUNTIME_LIMIT,
            "verifierAcceptedLanguageGuaranteesBelow1400000": False,
            "safeToPromoteAsUniversalCuPolicy": False,
            "reasonNotProductionPromoted": (
                "the closure is implemented behind default-off audit features and uses audit-only "
                "identities on disposable local clusters; release migration and production identity "
                "selection are explicitly outside this task"
            ),
            "byteIdenticalSimulationStillRequired": True,
            "classification": release_classification,
        },
        "scope": {
            "productionSourceChanged": True,
            "verifierChanged": True,
            "proofFormatChanged": False,
            "relationChanged": False,
            "cpiOrderingChanged": False,
            "poolExistingAccountLayoutChanged": False,
            "newVerifierOwnedCertificateAccountBytes": 704,
            "terminalWireByteDelta": 33,
            "auditFeaturesDefaultOff": True,
            "publicDevnetEvidenceModified": False,
            "publicDeploymentPerformed": False,
            "mainnetReady": False,
        },
    })

    json.dump(result, sys.stdout, indent=2 if args.pretty else None, sort_keys=True)
    sys.stdout.write("\n")


if __name__ == "__main__":
    main()
