#!/usr/bin/env python3
"""Fail-closed inventory of successful V7 terminal PDA searches.

The output enumerates the production-shaped immutable-Registry-V2 call graph.
It is an inventory, not a CU bound: each row remains variable until its named
authentication replacement is implemented and source-proved.
"""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def source_has(path: str, pattern: str) -> None:
    text = (ROOT / path).read_text(encoding="utf-8")
    if re.search(pattern, text, re.MULTILINE | re.DOTALL) is None:
        raise SystemExit(f"FAIL: missing PDA inventory anchor {path}: {pattern}")


def row(
    call_id: str,
    component: str,
    path: str,
    function: str,
    caller: str,
    program_id: str,
    seeds: list[dict[str, str]],
    expected_account_supplied: bool,
    bump_storage: str,
    duplicate_group: str | None,
    security_role: str,
    replacement_class: str,
    *,
    rollover_only: bool = False,
    withdrawal_only: bool = False,
) -> dict[str, object]:
    return {
        "callId": call_id,
        "component": component,
        "source": {"file": path, "function": function, "caller": caller},
        "programId": program_id,
        "seeds": seeds,
        "seedClass": "derived" if any(seed["class"] == "derived" for seed in seeds) else "static",
        "expectedPdaAlreadySuppliedAsAccount": expected_account_supplied,
        "bumpStorageBeforeChange": bump_storage,
        "duplicateIdentityGroup": duplicate_group,
        "bumpChangesDuringObjectLifetime": False,
        "securityRole": security_role,
        "candidateReplacementClass": replacement_class,
        "applies": {
            "samePageTransfer": not rollover_only and not withdrawal_only,
            "rolloverTransfer": not withdrawal_only,
            "samePageWithdrawal": not rollover_only,
            "rolloverWithdrawal": True,
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args()

    anchors = [
        ("programs/aspis-pool/src/pair_forest.rs", r"fn decode_master_account\(.*pool_v1_pair_forest_master_address"),
        ("programs/aspis-pool/src/pair_forest.rs", r"fn decode_lane_account\(.*pool_v1_pair_forest_lane_address"),
        ("programs/aspis-pool/src/pair_forest.rs", r"fn validate_pair_forest_request_accounts_v1\(.*pool_v1_pair_forest_lane_address"),
        ("programs/aspis-pool/src/pair_forest.rs", r"fn decode_retained_pair_forest_checkpoint_account_v1\(.*pool_v1_pair_forest_checkpoint_address"),
        ("programs/aspis-pool/src/history.rs", r"fn require_root_page_address\(.*pool_v1_root_page_address"),
        ("programs/aspis-pool/src/nullifier.rs", r"fn plan_nullifier_marker_consumption_v1\(.*pool_v1_nullifier_marker_address"),
        ("programs/aspis-pool/src/processor.rs", r"fn create_nullifier_marker_if_needed_v1[^\n]*\(.*plan_nullifier_marker_consumption_v1"),
        ("programs/aspis-pool/src/vault.rs", r"fn plan_legacy_withdrawal_transfer_from_identity_v1\(.*pool_v1_vault_authority_address.*pool_v1_vault_token_account_address"),
        ("programs/aspis-pool/src/registry.rs", r"fn authenticate_verifier_selection_v2\(.*find_program_address"),
        ("programs/aspis-verifier/src/v7_pair_forest_dispatch.rs", r"fn authenticate_invariant_release_registry_at_slot_v1\(.*find_program_address"),
        ("programs/aspis-verifier/src/v7_pair_forest_dispatch.rs", r"fn authenticate_asq8_accounts_v1\(.*find_program_address"),
        ("programs/aspis-verifier/src/v7_terminal_pda_certificate.rs", r"fn require_canonical_bumps\(.*find_program_address"),
        ("programs/aspis-verifier/src/v7_terminal_pda_certificate.rs", r"fn require_created_address\(.*create_program_address"),
        ("programs/aspis-verifier/src/v7_terminal_pda_certificate.rs", r"fn process_initialize_terminal_pda_certificate_v1\(.*require_canonical_bumps.*validate_terminal_pda_certificate_single_attempt_v1.*destination\.copy_from_slice"),
        ("programs/aspis-pool/src/nullifier.rs", r"fn plan_nullifier_marker_consumption_with_bump_v1\(.*create_program_address"),
        ("programs/aspis-pool/src/vault.rs", r"fn plan_legacy_withdrawal_transfer_from_identity_with_bumps_v1\(.*create_program_address"),
        ("programs/aspis-pool/src/pair_forest_dispatch.rs", r"fn dispatch_pair_forest_terminal_with_certificate_readonly_v1"),
    ]
    for path, pattern in anchors:
        source_has(path, pattern)

    static = lambda value: {"value": value, "class": "static"}
    derived = lambda value: {"value": value, "class": "derived"}
    pool = "runtime Pool program id"
    registry = "master.verifier_policy.registry_program (fixed by audit release capability)"
    loader = "BPFLoaderUpgradeab1e11111111111111111111111"
    profile = "V7_POOL_PAIR_FOREST_TAG73_PROFILE_BINDING"
    release = "V7_POOL_PAIR_FOREST_TAG73_RELEASE_BINDING"

    rows = [
        row("pool.master", "Pool", "programs/aspis-pool/src/pair_forest.rs", "decode_master_account", "process_pair_forest_terminal_with_verifier_v1", pool, [static("aspis-pair-forest-master-v1"), derived("decoded master.identity.asset_mint")], True, "not stored", "master", "canonical Pool identity", "program-owned placement invariant"),
        row("pool.checkpoint", "Pool", "programs/aspis-pool/src/pair_forest.rs", "decode_retained_pair_forest_checkpoint_account_v1", "decode_terminal_checkpoint_box_v1", pool, [static("aspis-pair-forest-checkpoint-v1"), derived("supplied master key"), derived("decoded checkpoint_sequence LE")], True, "not stored", "checkpoint", "immutable retained checkpoint identity", "program-owned placement invariant"),
        row("pool.lane.decode", "Pool", "programs/aspis-pool/src/pair_forest.rs", "decode_lane_account[_from_program_invariant_v1]", "decode_terminal_lane_box_v1", pool, [static("aspis-pair-forest-lane-v1"), derived("supplied master key"), derived("output lane from canonical nullifier")], True, "not stored", "selected-lane", "selected live lane identity", "authenticated parent/source placement invariant"),
        row("pool.lane.request", "Pool", "programs/aspis-pool/src/pair_forest.rs", "validate_pair_forest_request_accounts_v1", "process_pair_forest_terminal_with_verifier_v1", pool, [static("aspis-pair-forest-lane-v1"), derived("supplied master key"), derived("output lane from canonical nullifier")], True, "not stored", "selected-lane", "duplicate selected-lane binding", "reuse prior authenticated equality"),
        row("pool.history.current", "Pool", "programs/aspis-pool/src/history.rs", "require_root_page_address", "plan_pair_forest_spend_layout_v1 via validate_lane_current_page", pool, [static("aspis-root-page-v1"), derived("authenticated selected lane key"), derived("current page number from lane next index")], True, "not stored", "current-history", "current retained-root page identity", "program-owned placement invariant"),
        row("pool.history.next", "Pool", "programs/aspis-pool/src/history.rs", "require_root_page_address", "plan_pair_forest_spend_layout_v1 rollover branch", pool, [static("aspis-root-page-v1"), derived("authenticated selected lane key"), derived("next page number from next index")], True, "not stored", None, "fresh rollover page identity", "bounded bump certificate at page preparation", rollover_only=True),
        row("pool.nullifier.pre", "Pool", "programs/aspis-pool/src/nullifier.rs", "plan_nullifier_marker_consumption_v1", "process_pair_forest_terminal_with_verifier_v1", pool, [static("aspis-nullifier-v1"), derived("authenticated master key"), derived("canonical public nullifier")], True, "held only in PlannedNullifierMarkerV1 during this instruction", "nullifier-marker", "canonical uniqueness; alternate bumps would permit replay", "preterminal verifier-owned canonical-bump certificate"),
        row("pool.vault.authority", "Pool", "programs/aspis-pool/src/vault.rs", "plan_legacy_withdrawal_transfer_from_identity_v1", "process_pair_forest_terminal_with_verifier_v1", pool, [static("aspis-pool-vault-authority-v1"), derived("authenticated master key")], True, "returned in withdrawal plan but not persisted", None, "SPL CPI signing authority", "persist canonical bump in master capability", withdrawal_only=True),
        row("pool.vault.token", "Pool", "programs/aspis-pool/src/vault.rs", "plan_legacy_withdrawal_transfer_from_identity_v1", "process_pair_forest_terminal_with_verifier_v1", pool, [static("aspis-pool-vault-token-v1"), derived("authenticated master key")], True, "not stored", None, "custody token-account identity", "persist canonical bump/address in master capability", withdrawal_only=True),
        row("pool.nullifier.post", "Pool", "programs/aspis-pool/src/nullifier.rs", "plan_nullifier_marker_consumption_v1", "create_nullifier_marker_if_needed_v1", pool, [static("aspis-nullifier-v1"), derived("authenticated master key"), derived("canonical public nullifier")], True, "same canonical bump already held in PlannedNullifierMarkerV1", "nullifier-marker", "post-create owner/size/zero/rent/payload recheck", "reuse prior canonical bump with create_program_address"),
        row("pool.registry.programdata", "Pool", "programs/aspis-pool/src/registry.rs", "authenticate_verifier_selection_v2", "plan_pair_forest_terminal_dispatch_v1", loader, [derived("fixed registry program id")], False, "address stored in decoded Registry V2; bump not stored", "registry-programdata", "immutable registry deployment certificate", "registry-creation provenance invariant"),
        row("pool.registry.account", "Pool", "programs/aspis-pool/src/registry.rs", "authenticate_verifier_selection_v2", "plan_pair_forest_terminal_dispatch_v1", registry, [static("aspis-verifier-registry-v2"), derived("authenticated master key")], True, "not stored", "registry-account", "canonical per-Pool registry identity", "registry-owned placement invariant"),
        row("pool.registry.entry", "Pool", "programs/aspis-pool/src/registry.rs", "authenticate_verifier_selection_v2", "plan_pair_forest_terminal_dispatch_v1", registry, [static("aspis-verifier-entry-v2"), derived("authenticated master key"), static(profile), static(release)], True, "not stored", "registry-entry", "exact profile/release certificate identity", "registry-owned placement invariant"),
        row("pool.verifier.programdata", "Pool", "programs/aspis-pool/src/registry.rs", "authenticate_verifier_selection_v2", "plan_pair_forest_terminal_dispatch_v1", loader, [derived("selected verifier program id")], False, "address stored in decoded Registry entry V2; bump not stored", "verifier-programdata", "immutable verifier deployment certificate", "entry-creation provenance invariant"),
        row("verifier.registry.account", "verifier", "programs/aspis-verifier/src/v7_pair_forest_dispatch.rs", "authenticate_invariant_release_registry_at_slot_v1", "authenticate_asq8_accounts_v1", registry, [static("aspis-verifier-registry-v2"), derived("authenticated master key")], True, "not stored", "registry-account", "direct-invocation registry authentication", "same registry-owned placement invariant"),
        row("verifier.registry.programdata", "verifier", "programs/aspis-verifier/src/v7_pair_forest_dispatch.rs", "authenticate_invariant_release_registry_at_slot_v1", "authenticate_asq8_accounts_v1", loader, [derived("fixed registry program id")], False, "address stored in decoded Registry V2; bump not stored", "registry-programdata", "direct-invocation immutable registry authentication", "same registry-creation provenance invariant"),
        row("verifier.registry.entry", "verifier", "programs/aspis-verifier/src/v7_pair_forest_dispatch.rs", "authenticate_invariant_release_registry_at_slot_v1", "authenticate_asq8_accounts_v1", registry, [static("aspis-verifier-entry-v2"), derived("authenticated master key"), static(profile), static(release)], True, "not stored", "registry-entry", "direct-invocation exact release authentication", "same registry-owned placement invariant"),
        row("verifier.verifier.programdata", "verifier", "programs/aspis-verifier/src/v7_pair_forest_dispatch.rs", "authenticate_invariant_release_registry_at_slot_v1", "authenticate_asq8_accounts_v1", loader, [derived("runtime verifier program id")], False, "address stored in decoded Registry entry V2; bump not stored", "verifier-programdata", "direct-invocation immutable self authentication", "same entry-creation provenance invariant"),
        row("verifier.master", "verifier", "programs/aspis-verifier/src/v7_pair_forest_dispatch.rs", "authenticate_asq8_accounts_v1", "process_v7_pair_forest_asq8_instruction", pool, [static("aspis-pair-forest-master-v1"), derived("decoded master.identity.asset_mint")], True, "not stored", "master", "direct-invocation Pool master authentication", "same program-owned placement invariant"),
        row("verifier.checkpoint", "verifier", "programs/aspis-verifier/src/v7_pair_forest_dispatch.rs", "authenticate_asq8_accounts_v1", "process_v7_pair_forest_asq8_instruction", pool, [static("aspis-pair-forest-checkpoint-v1"), derived("supplied master key"), derived("decoded checkpoint_sequence LE")], True, "not stored", "checkpoint", "direct-invocation retained checkpoint authentication", "same program-owned placement invariant"),
        row("verifier.lane", "verifier", "programs/aspis-verifier/src/v7_pair_forest_dispatch.rs", "authenticate_asq8_accounts_v1", "process_v7_pair_forest_asq8_instruction", pool, [static("aspis-pair-forest-lane-v1"), derived("supplied master key"), derived("output lane from canonical nullifier")], True, "not stored", "selected-lane", "direct-invocation selected live lane authentication", "same authenticated parent/source placement invariant"),
    ]

    counts = {shape: sum(bool(item["applies"][shape]) for item in rows) for shape in rows[0]["applies"]}
    expected = {"samePageTransfer": 18, "rolloverTransfer": 19, "samePageWithdrawal": 20, "rolloverWithdrawal": 21}
    if counts != expected:
        raise SystemExit(f"FAIL: terminal PDA totals changed: {counts} != {expected}")
    closure_identities = [
        {"identity": "Pool master", "certificateSlot": 0, "terminalSingleAttempts": 1, "applies": "all"},
        {"identity": "retained checkpoint", "certificateSlot": 1, "terminalSingleAttempts": 1, "applies": "all"},
        {"identity": "selected lane", "certificateSlot": 2, "terminalSingleAttempts": 1, "applies": "all"},
        {"identity": "current history page", "certificateSlot": 3, "terminalSingleAttempts": 1, "applies": "all"},
        {"identity": "next history page", "certificateSlot": 4, "terminalSingleAttempts": 1, "applies": "rollover"},
        {"identity": "nullifier marker", "certificateSlot": 5, "terminalSingleAttempts": 3, "applies": "all", "reason": "certificate replay plus Pool pre-create and post-create checks"},
        {"identity": "Registry V2", "certificateSlot": 6, "terminalSingleAttempts": 1, "applies": "all"},
        {"identity": "Registry ProgramData", "certificateSlot": 7, "terminalSingleAttempts": 1, "applies": "all"},
        {"identity": "Registry V2 entry", "certificateSlot": 8, "terminalSingleAttempts": 1, "applies": "all"},
        {"identity": "verifier ProgramData", "certificateSlot": 9, "terminalSingleAttempts": 1, "applies": "all"},
        {"identity": "vault authority", "certificateSlot": 10, "terminalSingleAttempts": 2, "applies": "withdrawal", "reason": "certificate replay plus Pool SPL-CPI plan check"},
        {"identity": "vault token account", "certificateSlot": 11, "terminalSingleAttempts": 2, "applies": "withdrawal", "reason": "certificate replay plus Pool custody plan check"},
    ]
    fixed_counts = {
        "samePageTransfer": 11,
        "rolloverTransfer": 12,
        "samePageWithdrawal": 15,
        "rolloverWithdrawal": 16,
    }
    result = {
        "schema": "aspis.v7.terminal-pda-inventory.v2",
        "repositoryStartingRevision": "e5640f79133f8afbeb7eb08a940abc6462274295",
        "registryFamily": "immutable-v2",
        "counts": counts,
        "rows": rows,
        "authenticatedFixedBumpClosure": {
            "feature": "v7-terminal-pda-certificate-audit / pair-forest-terminal-pda-certificate-audit",
            "defaultOff": True,
            "certificateMagic": "APD8",
            "certificateOwner": "selected verifier program",
            "certificateWritableDuringTerminal": False,
            "canonicalSearchLocation": "process_initialize_terminal_pda_certificate_v1 before the terminal transaction",
            "terminalFindProgramAddressInvocations": {shape: 0 for shape in fixed_counts},
            "terminalSingleAttemptValidations": fixed_counts,
            "maximumTerminalSingleAttempts": max(fixed_counts.values()),
            "createProgramAddressCuPerAttempt": 1500,
            "maximumTerminalPdaSyscallCu": max(fixed_counts.values()) * 1500,
            "identities": closure_identities,
            "proofFormatChanged": False,
            "statementFormatChanged": False,
            "poolAccountLayoutChanged": False,
            "additionalTerminalReadonlyAccounts": 1,
            "terminalWireByteDelta": 33,
        },
        "conclusion": {
            "allCallsEquivalent": False,
            "dominantFreshIdentity": "pool.nullifier.pre",
            "sameInstructionDuplicate": "pool.nullifier.post",
            "securityWarning": "A supplied nullifier bump is not sufficient: alternate valid bumps would create replay namespaces.",
        },
    }
    print(json.dumps(result, indent=2 if args.pretty else None, sort_keys=True))


if __name__ == "__main__":
    main()
