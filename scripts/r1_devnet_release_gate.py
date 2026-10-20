#!/usr/bin/env python3
"""Read-only frozen-artifact/RPC gate; never signs or submits a transaction.

Exit 0 means the listed release/preflight checks pass, not that a spend works.
Exit 4 means a recorded release/preflight check failed. Existing receipts are
never overwritten. Key files are neither required nor opened.
"""
import base64
import hashlib
import json
from pathlib import Path
import struct
import sys
import time
import urllib.error
import urllib.request


def sha(data):
    return hashlib.sha256(data).hexdigest()


def base58(address):
    alphabet = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"
    n = 0
    for c in address:
        n = n * 58 + alphabet.index(c)
    value = b"\0" * (len(address) - len(address.lstrip("1")))
    value += n.to_bytes((n.bit_length() + 7) // 8, "big")
    if len(value) != 32:
        raise ValueError("program ID must decode to exactly 32 bytes")
    return value


def sections(data):
    if data[:6] != b"\x7fELF\x02\x01":
        raise ValueError("expected ELF64 little endian")
    offset = struct.unpack_from("<Q", data, 40)[0]
    stride, count, names = struct.unpack_from("<HHH", data, 58)
    headers = [struct.unpack_from("<IIQQQQIIQQ", data, offset + stride * i)
               for i in range(count)]
    strings = headers[names]
    result = {}
    for h in headers:
        start = strings[4] + h[0]
        name = data[start:data.index(b"\0", start)].decode()
        result[name] = {"offset": h[4], "bytes": h[5]}
    return result


def main():
    if len(sys.argv) != 3:
        sys.exit("usage: r1_devnet_release_gate.py CONFIG NEW_RECEIPT_DIR")
    config = json.loads(Path(sys.argv[1]).read_text())
    out = Path(sys.argv[2])
    out.mkdir(parents=True, exist_ok=False)

    def write(name, value):
        (out / name).write_text(json.dumps(value, indent=2) + "\n")

    write("config.json", config)
    started = time.monotonic()
    checks = {}
    artifacts = {}
    data = {}
    for role, spec in config["release_artifacts"].items():
        data[role] = Path(spec["path"]).read_bytes()
        artifacts[role] = {"path": spec["path"], "sha256": sha(data[role]),
                           "bytes": len(data[role]), "first_four_hex": data[role][:4].hex()}
        checks[role + "_documented_pin"] = sha(data[role]) == spec["sha256"]
    default, devnet = data["default_verifier"], data["devnet_verifier"]
    old_sections, new_sections = sections(default), sections(devnet)
    text = old_sections[".text"]
    new_text = new_sections[".text"]
    checks["section_layout_equal"] = old_sections == new_sections
    checks["text_identical"] = (
        default[text["offset"]:text["offset"] + text["bytes"]] ==
        devnet[new_text["offset"]:new_text["offset"] + new_text["bytes"]])
    expected = bytearray(default)
    slot_results = {}
    for role, placeholder in [("pool", 0x41), ("registry", 0x44)]:
        offset = config["deployment_slots"][role]
        slot_results[role] = {"offset": offset,
            "default_placeholder": default[offset:offset + 32] == bytes([placeholder]) * 32,
            "devnet_id": devnet[offset:offset + 32] == base58(config["programs"][role])}
        checks[role + "_slot"] = all(v for k, v in slot_results[role].items() if k != "offset")
        expected[offset:offset + 32] = base58(config["programs"][role])
    checks["only_two_slots_changed"] = bytes(expected) == devnet
    checks["declared_default_elf_pin"] = sha(default) == config["declared_default_elf_sha256"]
    write("identity.json", {"artifacts": artifacts, "default_sections": old_sections,
        "devnet_sections": new_sections, "slots": slot_results,
        "changed_bytes": sum(a != b for a, b in zip(default, devnet)), "checks": checks})

    def rpc(name, method, params):
        request = {"jsonrpc": "2.0", "id": 1, "method": method, "params": params}
        write(name + ".request.json", request)
        for attempt in range(4):
            begin = time.monotonic()
            status, raw = None, b""
            try:
                req = urllib.request.Request(config["rpc_url"], json.dumps(request).encode(),
                                             {"Content-Type": "application/json"})
                with urllib.request.urlopen(req, timeout=45) as response:
                    status, raw = response.status, response.read()
                result = json.loads(raw)
                write(f"{name}.{attempt}.response.json", result)
                write(f"{name}.{attempt}.timing.json", {"http_status": status,
                                                       "wall_seconds": time.monotonic() - begin})
                if "error" not in result:
                    return result["result"]
                if result["error"].get("code") not in (429, -32005):
                    raise RuntimeError(result["error"])
            except (urllib.error.URLError, TimeoutError) as error:
                if isinstance(error, urllib.error.HTTPError):
                    status, raw = error.code, error.read()
                write(f"{name}.{attempt}.error.json", {"http_status": status,
                    "body": raw.decode(errors="replace"), "error": str(error),
                    "wall_seconds": time.monotonic() - begin})
            if attempt < 3:
                time.sleep(2 ** attempt)
        raise RuntimeError(f"RPC retries exhausted: {name}")

    checks["devnet_genesis"] = rpc("genesis", "getGenesisHash", []) == config["genesis_hash"]
    version = rpc("version", "getVersion", [])
    feature = rpc("txv1-feature", "getAccountInfo", [config["txv1_feature"],
                    {"encoding": "base64", "commitment": "finalized"}])
    feature_account = feature["value"]
    activated_slot = None
    if feature_account and feature_account["owner"] == "Feature111111111111111111111111111111111111":
        feature_data = base64.b64decode(feature_account["data"][0])
        if len(feature_data) == 9 and feature_data[0] == 1:
            activated_slot = int.from_bytes(feature_data[1:], "little")
    checks["txv1_active"] = activated_slot is not None and activated_slot <= feature["context"]["slot"]
    roles = ["payer", "verifier", "pool", "registry"]
    addresses = [config["payer"]] + [config["programs"][role] for role in roles[1:]]
    accounts = rpc("accounts", "getMultipleAccounts", [addresses,
                   {"encoding": "base64", "commitment": "finalized"}])
    payer_lamports = accounts["value"][0]["lamports"] if accounts["value"][0] else 0
    rent = {}
    for role, artifact in [("verifier", "devnet_verifier"), ("pool", "pool"), ("registry", "registry")]:
        size = len(data[artifact]) + 45
        rent[role] = {"programdata_bytes": size,
            "programdata_lamports": rpc(role + "-rent", "getMinimumBalanceForRentExemption", [size]),
            "program_lamports": rpc(role + "-program-rent", "getMinimumBalanceForRentExemption", [36])}
    permanent_rent = sum(r["programdata_lamports"] + r["program_lamports"] for r in rent.values())
    checks["payer_covers_permanent_program_rent"] = payer_lamports > permanent_rent
    write("summary.json", {"schema": "aspis.r1.devnet-release-gate.v1", "read_only": True,
        "source_revision": config["source_revision"], "checks": checks,
        "passed": all(checks.values()), "version": version, "txv1_activation_slot": activated_slot,
        "accounts_context_slot": accounts["context"]["slot"], "payer_lamports": payer_lamports,
        "reserved_programs_absent": {r: a is None for r, a in zip(roles[1:], accounts["value"][1:])},
        "rent": rent, "permanent_program_rent_lamports": permanent_rent,
        "rent_note": "Excludes temporary loader buffers, fees, mint, pool state and proof accounts.",
        "wall_seconds": time.monotonic() - started, "spend_validated": False,
        "signatures_submitted": [], "print_axioms": "N/A (no Lean)"})
    print(json.dumps({"checks": checks, "passed": all(checks.values()), "payer_lamports": payer_lamports}))
    return 0 if all(checks.values()) else 4


if __name__ == "__main__":
    sys.exit(main())
