#!/usr/bin/env python3
"""Read-only pins for the inspected R17 host oracle-entrypoint slice.

Not a complete call graph, generated-source closure, query cap, or security
proof. No seeds, hash preimages, wallet keys, or runtime secrets are printed.
"""
import argparse
import hashlib
import json
from pathlib import Path

EXPERIMENTS = "docs/research/v8-no-work-100-20260907/experiments/"
PINS = {
    "r17-stage.json": "b6954128f7f09e9e75bcb2271c474e2749645262472bfc676126ec08b9825145",
    EXPERIMENTS + "performance.rs": "1000c12343e30eb33af82856a12d02daed168509ffb597ebdecaf63a6343b5f5",
    EXPERIMENTS + "performance_verifier.rs": "7355b60338911409ac51b5d4fa95bc334e49d37f3c8b49afb2c376a3d946634d",
    EXPERIMENTS + "relation_callback.rs": "22c0837ec4f14a0b9a3795b6bdc40144911468c5499836eca48cc503ce698b9e",
    EXPERIMENTS + "positive_transfer.rs": "3a19043d2f40f168cb2127ba46e1795db7ea0751625c4fe48c73e02dab533cab",
    "crates/aspis-prover/src/state_only_entropy.rs": "78ebbb3176daf23935243452992548ff9d877aaaf853d73e5ee46b60d8cb3ec0",
    "crates/aspis-prover/src/state_only_hiding.rs": "0e8b83d50aaebc65dad86bc63c838d099428a166221990156b9f61164148fe0a",
    "crates/aspis-core/src/transcript.rs": "be036d144b9fe0c8119d9f6fdd8ca2167d1379f7d1d785fa2f197200b9f7d119",
    "crates/aspis-core/src/state_only_hiding.rs": "18058112db3108a18f9d11f8d9ffb6f9c1b310b90b333010fd0f98cac480237f",
    "crates/aspis-core/src/v7_merkle208.rs": "071ade1236140fdae559bb7b607ac9b7ee299e74eccb16b3385e3b1bbf215fdf",
    "crates/aspis-core/src/state_only_private_merkle.rs": "f0edc31d07d30f5b19fcaf872fba18678d13d1ba5fac1199f1f4d2be74c74f9b",
}
TEST_SHIM = b'''
#[cfg(test)]
#[path = "r11_mask_material_kat.rs"]
mod r11_mask_material_kat;

#[cfg(test)]
#[path = "r13_source_bridge.rs"]
mod r13_source_bridge;
'''
CURRENT_HIDING = "48dddafce0ea55d5df2f6b670cd8c571cd182e446ce34ea8b3d42aa313b32d3f"


def digest(data):
    return hashlib.sha256(data).hexdigest()


def check(data, expected, name):
    actual = digest(data)
    if actual != expected:
        raise ValueError(f"source pin mismatch: {name}: {actual} != {expected}")
    return actual


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--stage", type=Path, required=True)
    parser.add_argument("--repo", type=Path, default=Path(__file__).resolve().parents[4])
    args = parser.parse_args()
    checks = []
    for path, expected in PINS.items():
        data = (args.stage / path).read_bytes()
        checks.append({"surface": "stage", "path": path,
                       "sha256": check(data, expected, path)})
        if path.startswith("crates/"):
            current = (args.repo / path).read_bytes()
            current_expected = CURRENT_HIDING if path == "crates/aspis-prover/src/state_only_hiding.rs" else expected
            checks.append({"surface": "worktree", "path": path,
                           "sha256": check(current, current_expected, path)})
            if current_expected != expected:
                if current.count(TEST_SHIM) != 1:
                    raise ValueError("expected exact test-only shim once")
                if current.replace(TEST_SHIM, b"", 1) != data:
                    raise ValueError("difference exceeds exact test-only module shim")
    metadata = json.loads((args.stage / "r17-stage.json").read_text())
    if metadata["complete_generated_closure"] is not False:
        raise ValueError("review changed generated-closure claim")
    if "insecure-spend-fixture" not in metadata["features"]:
        raise ValueError("review changed fixture/entropy profile")
    if "--cfg v8_performance_sbf" in metadata["rustflags"]:
        raise ValueError("not the audited host profile")
    print(json.dumps({
        "status": "INSPECTED_SOURCE_PINS_MATCH",
        "checks": checks,
        "scope": "selected host mask/salt/D/transcript/Merkle entrypoint slice",
        "complete_call_graph": False,
        "complete_generated_closure": False,
        "source_probability_theorem": False,
        "production_entropy_or_publication": False,
        "direct_sha_outside_callback": "DurableStateOnlyMaskNonceStore.reservation_path; not used by this in-memory fixture",
    }, indent=2))


if __name__ == "__main__":
    main()
