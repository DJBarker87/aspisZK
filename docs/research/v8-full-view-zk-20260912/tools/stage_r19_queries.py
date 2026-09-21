#!/usr/bin/env python3
"""Stage the optional R19 same-profile shared-query adapter.

The adapter is intentionally additive: it authenticates every file recorded by
the R18 manifest, copies that stage unchanged, and installs only the query
adapter and its focused production-accumulator checker.  It does not alter the
proof layout, transcript labels, base channels, or the old increment encoding.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import shutil
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
EXPERIMENTS = "docs/research/v8-no-work-100-20260907/experiments"
PACKET = Path("/Users/dominic/Downloads/aspis-r19-channel-fold-20260921")
REPO_PACKET = ROOT / "docs/research/v8-full-view-zk-20260912/r19-pack"
PACKET_SHARED_SHA256 = "a1325eaf3964471e327aadbdb09db239a335baf3983d78d3e481b244f4e2e4cd"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--stage", type=Path, required=True,
                        help="authenticated R18 stage directory")
    parser.add_argument("--output", type=Path, required=True,
                        help="new stage directory (must not already exist)")
    args = parser.parse_args()
    stage = args.stage.resolve()
    output = args.output.resolve()
    if output.exists():
        raise SystemExit(f"refusing to overwrite existing output: {output}")
    manifest_path = stage / "r18-stage.json"
    if not manifest_path.is_file():
        raise SystemExit(f"missing R18 manifest: {manifest_path}")
    manifest = json.loads(manifest_path.read_text())
    if not manifest.get("compact_primary"):
        raise SystemExit("R18 manifest is not a compact primary stage")
    if manifest.get("profile") != "AV8/R18/sparse-coded-G128-step3/minimal-T163/research-v2":
        raise SystemExit("unexpected R18 profile in stage manifest")
    for name, expected in manifest.get("files", {}).items():
        path = stage / name
        if not path.is_file() or digest(path) != expected:
            raise SystemExit(f"R18 manifest mismatch: {name}")

    source = REPO_PACKET / "src/shared_queries.rs"
    if not source.is_file():
        source = PACKET / "src/shared_queries.rs"
    if not source.is_file():
        raise SystemExit(f"missing shared-query source: {source}")
    if digest(source) != PACKET_SHARED_SHA256:
        raise SystemExit(f"shared-query source hash mismatch: {source}")
    checker = Path(__file__).with_name("r19_query_shared_check.rs")
    if not checker.is_file():
        raise SystemExit(f"missing checker beside adapter: {checker}")

    shutil.copytree(stage, output)
    root = output / EXPERIMENTS
    shutil.copy2(source, root / "r19_shared_queries.rs")
    shutil.copy2(checker, root / "r19_query_shared_check.rs")

    host = root / "r17_host_relation.rs"
    host_text = host.read_text()
    anchor = "use super::*;\n"
    if anchor not in host_text:
        raise SystemExit("R18 host relation integration anchor missing")
    host_text = host_text.replace(anchor, anchor +
        '#[path="r19_shared_queries.rs"] mod r19_shared_queries;\n', 1)
    host_text = host_text.replace(
        "    let inc = if reference {\n",
        "    let mut query_lambda = K::ZERO;\n    let inc = if reference {\n", 1)
    old_injection = (
        "    } else {\n"
        "        inject_two(&mut weights, &mut claim, &values, &xs, rho)?\n"
        "    };\n")
    new_injection = (
        "    } else {\n"
        "        // Base A/E/G and image channels remain separate; only query\n"
        "        // covectors share storage after alpha0.\n"
        "        let prepared = r19_shared_queries::prepare(\n"
        "            &xs, values[0].as_slice().try_into().map_err(|_| Error::Shape)?,\n"
        "            values[1].as_slice().try_into().map_err(|_| Error::Shape)?, rho)\n"
        "            .ok_or(Error::Shape)?;\n"
        "        query_lambda = prepared.lambda;\n"
        "        weights[0] = prepared.weights;\n"
        "        claim = claim.add(prepared.increment);\n"
        "        prepared.increment\n"
        "    };\n")
    if old_injection not in host_text:
        raise SystemExit("R18 injection block missing")
    host_text = host_text.replace(old_injection, new_injection, 1)
    old_fold = (
        "            } else {\n"
        "                weights[c].fold_deferred_relation_arity4(a);\n"
        "            }\n")
    new_fold = (
        "            } else if c == 0 {\n"
        "                weights[0].fold_deferred_relation_arity4(a);\n"
        "            }\n")
    if old_fold not in host_text:
        raise SystemExit("R18 fold block missing")
    host_text = host_text.replace(old_fold, new_fold, 1)
    old_terminal = (
        "    let mut terminal=(0..2).fold(K::ZERO,|sum,c| {\n"
        "        let w=if reference {core::array::from_fn(|i|dense[c][i])}\n"
        "              else {weights[c].weight_prefix::<4>()};\n"
        "        sum.add(corelib::field::qm31_sum_products4(w,core::array::from_fn(|i|finals[c][i])))\n"
        "    });\n")
    new_terminal = (
        "    let mut terminal = if reference {\n"
        "        (0..2).fold(K::ZERO, |sum, c| {\n"
        "            let w = core::array::from_fn(|i| dense[c][i]);\n"
        "            sum.add(corelib::field::qm31_sum_products4(\n"
        "                w, core::array::from_fn(|i| finals[c][i])))\n"
        "        })\n"
        "    } else {\n"
        "        let query = weights[0].weight_prefix::<4>();\n"
        "        let combined = core::array::from_fn(|i| {\n"
        "            finals[0][i].add(query_lambda.mul(finals[1][i]))\n"
        "        });\n"
        "        corelib::field::qm31_sum_products4(query, combined)\n"
        "    };\n")
    if old_terminal not in host_text:
        raise SystemExit("R18 terminal query block missing")
    host.write_text(host_text.replace(old_terminal, new_terminal, 1))

    cargo = root / "performance-host/Cargo.toml"
    cargo_text = cargo.read_text()
    marker = 'name="r19-query-shared-check"'
    if marker not in cargo_text:
        cargo.write_text(cargo_text +
            '\n[[bin]]\nname="r19-query-shared-check"\n'
            'path="../r19_query_shared_check.rs"\n')

    new_profile = manifest["profile"]
    out_manifest = json.loads(manifest_path.read_text())
    updated_files = {name: digest(output / name) for name in manifest["files"]}
    updated_files.update({
        "docs/research/v8-no-work-100-20260907/experiments/r17_host_relation.rs":
            digest(root / "r17_host_relation.rs"),
        "docs/research/v8-no-work-100-20260907/experiments/performance-host/Cargo.toml":
            digest(root / "performance-host/Cargo.toml"),
        "docs/research/v8-no-work-100-20260907/experiments/r19_shared_queries.rs":
            digest(root / "r19_shared_queries.rs"),
        "docs/research/v8-no-work-100-20260907/experiments/r19_query_shared_check.rs":
            digest(root / "r19_query_shared_check.rs"),
    })
    out_manifest.update({
        "profile": new_profile,
        "predecessor": str(stage),
        "source_revision": manifest.get("source_revision"),
        "transcript_unchanged": True,
        "base_channels_unchanged": True,
        "r19_query_adapter": {
            "lambda": "scales[21] = rho^22; no division",
            "insertion": "after alpha0",
            "post_injection_folds": 3,
            "old_increment_bytes": True,
            "checker": "r19_query_shared_check",
        },
        "files": updated_files,
    })
    (output / "r18-stage.json").write_text(json.dumps(out_manifest, indent=2) + "\n")
    (output / "r19-stage.json").write_text(json.dumps(out_manifest, indent=2) + "\n")
    print(json.dumps({"stage": str(output), "profile": new_profile,
                      "transcript_unchanged": True, "r18_manifest": str(manifest_path)}))


if __name__ == "__main__":
    main()
