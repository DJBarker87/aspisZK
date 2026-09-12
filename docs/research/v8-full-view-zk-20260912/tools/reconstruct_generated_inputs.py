#!/usr/bin/env python3
"""Reconstruct locally available positive-COMPLETE generated inputs.

This is a non-destructive, portable replay. It never invokes the original
absolute-path integration/deployment script and fails closed when a required
preimage is unavailable.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil


TARGET = Path("docs/research/v8-positive-complete-devnet-20260909")
EXPERIMENTS = Path("docs/research/v8-no-work-100-20260907/experiments")


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def one_replace(text: str, old: str, new: str, label: str) -> str:
    count = text.count(old)
    if count != 1:
        raise ValueError(f"{label}: expected one occurrence, found {count}")
    return text.replace(old, new)


def write_stage(root: Path, relative: Path, text: str) -> Path:
    target = root / relative
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(text)
    return target


def transform_complete_binding(text: str) -> str:
    profile = b"aspis:research:v8:positive-transfer:qm31-q22:asq8-asf8-asr8:v1"
    release = b"aspis:research:v8:positive-transfer:lane94:mask3802:40282:image:shifted-rows:complete-v1"
    for name, preimage in (("PROFILE", profile), ("RELEASE", release)):
        text, count = re.subn(
            r"(pub const V7_POOL_PAIR_FOREST_TAG73_" + name + r'_BINDING_PREIMAGE: &\[u8\] = )b"[^"]*";',
            lambda match: match[1] + 'b"' + preimage.decode() + '";',
            text,
        )
        if count != 1:
            raise ValueError(f"complete_binding {name} preimage: {count}")
        text, count = re.subn(
            r"(pub const V7_POOL_PAIR_FOREST_TAG73_" + name + r"_BINDING: \[u8;32\] = )\[[^;]+\];",
            lambda match: match[1] + str(list(hashlib.sha256(preimage).digest())) + ";",
            text,
        )
        if count != 1:
            raise ValueError(f"complete_binding {name} digest: {count}")
    return text


def transform_positive(text: str) -> str:
    parent = bytes([
        121, 147, 51, 56, 96, 194, 205, 16, 170, 24, 62, 117, 31, 39, 16,
        186, 39, 155, 51, 42, 187, 191, 221, 206, 119, 59, 50, 23, 103, 240,
        1, 186,
    ])
    descriptor = (
        b"AV8/positive-transfer/active-cell-overwrite/lane94/v1"
        + parent
        + (1014).to_bytes(2, "little")
        + bytes([3, 94])
        + bytes.fromhex("f9daf3d54f4285d1")[::-1]
        + bytes.fromhex("6b661245a56c7189")[::-1]
        + (3802).to_bytes(2, "little")
    )
    assert len(descriptor) == 107
    text = one_replace(
        text,
        "d.extend(V7_POOL_PAIR_FOREST_TAG73_PROFILE_BINDING);",
        "d.extend(" + str(list(parent)) + ");",
        "positive parent",
    )
    text = one_replace(
        text,
        "pub fn descriptor()->Vec<u8>{",
        "pub const FROZEN_DESCRIPTOR: [u8;107] = "
        + str(list(descriptor))
        + ";\n#[cfg(v8_performance_sbf)]\npub fn descriptor()->Vec<u8>{ FROZEN_DESCRIPTOR.to_vec() }\n#[cfg(not(v8_performance_sbf))]\npub fn descriptor()->Vec<u8>{",
        "positive descriptor",
    )
    text = one_replace(text, "    d\n}", "    assert_eq!(d,FROZEN_DESCRIPTOR); d\n}", "positive descriptor check")
    text = one_replace(
        text,
        "use aspis_statement::{pool_v1::*, StateOnlyTraceFoundation};",
        "use aspis_statement::pool_v1::*;\n#[cfg(not(v8_performance_sbf))] use aspis_statement::StateOnlyTraceFoundation;",
        "positive imports",
    )
    for signature in ("pub fn mask_cells()", "fn fingerprint(", "pub fn install("):
        text = one_replace(
            text,
            signature,
            "#[cfg(not(v8_performance_sbf))]\n" + signature,
            f"positive cfg {signature}",
        )
    return text


def transform_performance(text: str) -> str:
    text = one_replace(
        text,
        "use super::*;",
        'use super::*;\n#[path="../../v8-positive-complete-devnet-20260909/live_context.rs"] mod live_context;',
        "performance live module",
    )
    text = one_replace(
        text,
        "let(public,witness,mut snapshot)=we::fixture();",
        'let(public,witness,mut snapshot)=if std::env::var_os("ASPIS_V8_LIVE_CONTEXT").is_some(){live_context::load()}else{we::fixture()};',
        "performance context",
    )
    text = one_replace(
        text,
        "let mut runtime=provision_accounts(&witness);",
        'let mut runtime=provision_accounts(&witness);\n    if std::env::var_os("ASPIS_V8_LIVE_CONTEXT").is_some(){assert_eq!(runtime.anchor_root,public.anchor_root);runtime.pool=public.pool;runtime.deployment_domain=public.deployment_domain;runtime.anchor_sequence=public.anchor_sequence;}',
        "performance runtime",
    )
    text = one_replace(text, "let complete_context=", "let mut complete_context=", "performance mutable context")
    text = one_replace(
        text,
        'assert!(complete_context.is_none(),"new positivity profile is not integrated with complete transaction wrapper");',
        'assert!(matches!(payment,PoolV1PairForestTerminalPaymentV1::PrivateTransfer(_)),"transfer-only profile");',
        "performance transfer-only",
    )
    text = one_replace(
        text,
        "    #[cfg(v8_positive_transfer)] let positive_case=",
        "    if let Some((statement,_))=&complete_context{assert_eq!(compiled.public_statement,statement.common().lane_transition); }\n    #[cfg(v8_positive_transfer)] let positive_case=",
        "performance context assertion",
    )
    text = one_replace(
        text,
        "let transition=compiled.public_statement;",
        '''let transition=compiled.public_statement;
    #[cfg(v8_positive_transfer)] if let Some((statement,attempt))=&mut complete_context {
        let PoolV1PairForestTerminalPaymentV1::PrivateTransfer(p)=payment else{panic!("transfer only")};
        let mut common=*statement.common();common.lane_transition=transition;
        *statement=PoolV1PairForestTerminalStatementV1::PrivateTransfer{public:p,common};
        let sb=encode_pool_v1_pair_forest_terminal_statement_v1(statement).unwrap();
        let digest=v7_pool_pair_forest_tag73_statement_digest_v1(&sb,hash);
        let dir=std::env::var("ASPIS_V8_COMPLETE_CONTEXT").unwrap();
        let vk:[u8;32]=std::fs::read(format!("{dir}/verifier.bin")).unwrap().try_into().unwrap();
        let pk:[u8;32]=std::fs::read(format!("{dir}/proof-account.bin")).unwrap().try_into().unwrap();
        *attempt=complete_binding::bind_attempt(hash,&digest,&vk,&pk);
        std::fs::write(format!("{out}/statement.bin"),sb).unwrap();
    }''',
        "performance statement rebind",
    )
    text = one_replace(
        text,
        "    for seed in seeds {",
        '    assert!(std::env::var_os("ASPIS_V8_MAX_FRONTIER_SCAN").is_none());\n    for seed in seeds {',
        "performance scan disable",
    )
    text = one_replace(
        text,
        "            continue;",
        '            std::fs::write(format!("{out}/proof-{seed}.bin"),&body).unwrap();\n            continue;',
        "performance rejected proof persistence",
    )
    return text


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    repo = args.repo.resolve()
    out = args.output.resolve()
    if out.exists():
        parser.error("output must not exist")
    out.mkdir(parents=True)

    manifest = json.loads((repo / TARGET / "integration-inputs.json").read_text())
    reconstructors = {
        EXPERIMENTS / "performance.rs": (
            TARGET / "upstream/performance.rs",
            transform_performance,
        ),
        EXPERIMENTS / "performance_verifier.rs": (
            TARGET / "upstream/performance_verifier.rs",
            lambda value: value,
        ),
        EXPERIMENTS / "relation_callback.rs": (
            TARGET / "upstream/relation_callback.rs",
            lambda value: value,
        ),
        EXPERIMENTS / "payment_extraction.rs": (
            TARGET / "upstream/payment_extraction.rs",
            lambda value: value,
        ),
        EXPERIMENTS / "complete_binding.rs": (
            EXPERIMENTS / "complete_binding.rs",
            transform_complete_binding,
        ),
        EXPERIMENTS / "positive_transfer.rs": (
            TARGET / "upstream/positive_transfer.rs",
            transform_positive,
        ),
        EXPERIMENTS / "run_complete_build_nuc.sh": (
            EXPERIMENTS / "run_complete_build_nuc.sh",
            lambda value: one_replace(
                one_replace(
                    value,
                    "readonly common='",
                    "readonly common='--cfg v8_positive_transfer ",
                    "build positive cfg",
                ),
                'terminal-prefix|terminal-fixed|terminal-fused|terminal-stack) bash "$complete_exp/check_terminal_query_sources.sh" "$mode";;',
                'terminal-prefix|terminal-fixed|terminal-fused|terminal-stack) python3 "$complete_root/docs/research/v8-positive-complete-devnet-20260909/check_inputs.py";;',
                "build source checker",
            ),
        ),
    }

    checks = []
    for raw_path, expected in manifest.items():
        relative = Path(raw_path)
        if relative not in reconstructors:
            checks.append({
                "path": raw_path,
                "status": "UNAVAILABLE_PREIMAGE",
                "required_before_sha256": expected["before"],
                "required_after_sha256": expected["after"],
            })
            continue
        source, transform = reconstructors[relative]
        source_path = repo / source
        source_hash = sha256(source_path)
        text = transform(source_path.read_text())
        staged = write_stage(out, relative, text)
        after_hash = sha256(staged)
        status = "PASS" if after_hash == expected["after"] else "MISMATCH"
        checks.append({
            "path": raw_path,
            "status": status,
            "source_path": str(source),
            "source_sha256": source_hash,
            "expected_after_sha256": expected["after"],
            "actual_after_sha256": after_hash,
        })

    passes = sum(item["status"] == "PASS" for item in checks)
    unavailable = sum(item["status"] == "UNAVAILABLE_PREIMAGE" for item in checks)
    complete = passes == len(checks)
    report = {
        "schema": "aspis.v8.positive-complete.portable-reconstruction.v1",
        "target_commit": "9e432896a4e1515efebe940b71fd9b4f9f009189",
        "checks": checks,
        "passes": passes,
        "unavailable_preimages": unavailable,
        "complete": complete,
        "scope": "generated input files only; no build, ELF or deployment",
    }
    (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({
        "report": str(out / "report.json"),
        "passes": passes,
        "unavailable_preimages": unavailable,
        "complete": complete,
    }))
    return 0 if complete else 2


if __name__ == "__main__":
    raise SystemExit(main())
