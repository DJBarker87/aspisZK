#!/usr/bin/env python3
"""Read-only, fail-closed TxV1 feature snapshot for public Solana clusters."""

from __future__ import annotations

import argparse
import base64
import datetime as dt
import json
import struct
import sys
import urllib.request


FEATURE_ID = "txv1aq4pp281K9um3tnPgkfX8UqtFT6wcVW3hNezGLL"
FEATURE_OWNER = "Feature111111111111111111111111111111111111"
ENDPOINTS = {
    "testnet": "https://api.testnet.solana.com",
    "devnet": "https://api.devnet.solana.com",
    "mainnet-beta": "https://api.mainnet-beta.solana.com",
}


def rpc(endpoint: str, method: str, params: list[object] | None = None) -> object:
    body = json.dumps(
        {"jsonrpc": "2.0", "id": 1, "method": method, "params": params or []},
        separators=(",", ":"),
    ).encode()
    request = urllib.request.Request(
        endpoint,
        data=body,
        headers={"Content-Type": "application/json"},
        method="POST",
    )
    with urllib.request.urlopen(request, timeout=20) as response:
        decoded = json.load(response)
    if decoded.get("error") is not None or "result" not in decoded:
        raise RuntimeError(f"{method} failed at {endpoint}: {decoded!r}")
    return decoded["result"]


def epoch_for_slot(slot: int, schedule: dict[str, object]) -> int:
    first_normal_slot = int(schedule["firstNormalSlot"])
    if slot < first_normal_slot:
        raise RuntimeError("feature activated during warmup; unsupported fail-closed case")
    return int(schedule["firstNormalEpoch"]) + (
        slot - first_normal_slot
    ) // int(schedule["slotsPerEpoch"])


def inspect_cluster(name: str, endpoint: str) -> dict[str, object]:
    account_result = rpc(
        endpoint,
        "getAccountInfo",
        [FEATURE_ID, {"encoding": "base64", "commitment": "finalized"}],
    )
    if not isinstance(account_result, dict):
        raise RuntimeError(f"unexpected getAccountInfo result at {endpoint}")
    account = account_result.get("value")
    schedule = rpc(endpoint, "getEpochSchedule")
    result: dict[str, object] = {
        "cluster": name,
        "rpcUrl": endpoint,
        "genesisHash": rpc(endpoint, "getGenesisHash"),
        "version": rpc(endpoint, "getVersion"),
        "epochInfo": rpc(endpoint, "getEpochInfo", [{"commitment": "finalized"}]),
        "epochSchedule": schedule,
        "featureId": FEATURE_ID,
        "featureOwnerExpected": FEATURE_OWNER,
        "featureAccountPresent": account is not None,
        "active": False,
        "activationSlot": None,
        "activationEpoch": None,
        "activationBlockTimeUnix": None,
        "activationBlockTimeUtc": None,
        "featureAccount": account,
    }
    if account is None:
        return result
    if not isinstance(account, dict) or account.get("owner") != FEATURE_OWNER:
        raise RuntimeError(f"feature account owner mismatch at {endpoint}")
    encoded = account.get("data")
    if not isinstance(encoded, list) or len(encoded) != 2 or encoded[1] != "base64":
        raise RuntimeError(f"feature account encoding mismatch at {endpoint}")
    raw = base64.b64decode(encoded[0], validate=True)
    # solana_feature_gate_interface::Feature stores bincode Option<u64>.
    if len(raw) != 9 or raw[0] not in (0, 1):
        raise RuntimeError(f"feature account data mismatch at {endpoint}: {raw.hex()}")
    result["featureDataHex"] = raw.hex()
    if raw[0] == 0:
        return result
    activation_slot = struct.unpack("<Q", raw[1:])[0]
    block_time = rpc(endpoint, "getBlockTime", [activation_slot])
    result.update(
        {
            "active": True,
            "activationSlot": activation_slot,
            "activationEpoch": epoch_for_slot(activation_slot, schedule),
            "activationBlockTimeUnix": block_time,
            "activationBlockTimeUtc": (
                dt.datetime.fromtimestamp(int(block_time), tz=dt.timezone.utc)
                .isoformat()
                .replace("+00:00", "Z")
                if block_time is not None
                else None
            ),
        }
    )
    return result


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--cluster",
        choices=["all", *ENDPOINTS],
        default="all",
        help="public RPC cluster to inspect (default: all)",
    )
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args()
    selected = ENDPOINTS if args.cluster == "all" else {args.cluster: ENDPOINTS[args.cluster]}
    result = {
        "schema": "aspis.v7.txv1-public-cluster-snapshot.v1",
        "observedAtUtc": dt.datetime.now(tz=dt.timezone.utc)
        .isoformat()
        .replace("+00:00", "Z"),
        "commitment": "finalized",
        "featureId": FEATURE_ID,
        "authoritativeStateRule": (
            "the feature account must exist, be owned by the Feature program, and encode "
            "bincode Some(activation_slot)"
        ),
        "officialStatusPage": "https://solana.com/upgrades/larger-transaction-sizes",
        "clusters": [inspect_cluster(name, endpoint) for name, endpoint in selected.items()],
    }
    json.dump(result, sys.stdout, indent=2 if args.pretty else None, sort_keys=True)
    sys.stdout.write("\n")


if __name__ == "__main__":
    main()
