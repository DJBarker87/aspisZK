import hashlib, json, pathlib

base = pathlib.Path(__file__).resolve().parent.parent
out = pathlib.Path(__file__).resolve().parent
src = out / "source"
fp = json.loads((src / "bin-charon-driver.json").read_text())
dep_artifacts = json.loads((out / "cached-dependency-artifacts.json").read_text())
link = json.loads((out / "build-script-link-directives.json").read_text())
cmd_path = base / "clone-build-preflight/build-attempt-v2/build-command.json"
result_path = base / "clone-build-preflight/build-attempt-v2/build-result.json"
log_path = base / "clone-build-preflight/build-attempt-v2/build.log"
cmd = json.loads(cmd_path.read_text())
result = json.loads(result_path.read_text())
cache = json.loads((base / "clone-launch-v2/clone-audit/target-cache-sha256.json").read_text())
cache_by_path = {x["path"]: x for x in cache}
psm = cache_by_path["release/build/psm-0054b740d3e1ad34/out/libpsm_s.a"]
externs = []
modules = []
for line in (src / "charon-driver-main.rs").read_text().splitlines():
    if line.startswith("extern crate "):
        externs.append(line.removeprefix("extern crate ").removesuffix(";"))
    if line.startswith("mod "):
        modules.append(line.removeprefix("mod ").removesuffix(";"))
source_files = {}
for f in sorted(src.iterdir()):
    if f.is_file():
        source_files[f.name] = {"sha256": hashlib.sha256(f.read_bytes()).hexdigest(), "bytes": f.stat().st_size}

report = {
  "classification": "Read-only inventory of pinned sources, saved original release cache, and stopped build-v2 evidence. No replacement invocation designed or launched.",
  "pinned_source": {
    "repository": "/home/dombarker/project-offloads/ZK-v5-formal/toolchains/charon",
    "revision": "cb50ff16b9f1066b8a97dc06da704de2da2fa41c",
    "cargo_manifest": "charon/Cargo.toml",
    "cargo_manifest_sha256": "a31bab7d34638f8c2a43f14263184a3328ab17366c2f9acf201d86b922c4176f",
    "cargo_lock_sha256": "c755a326679e9b3dbce560ff15130bdc83ae16178f2c1af568e391b8470d2e67",
    "toolchain": "nightly-2026-06-01",
    "rustc_commit": "14210df0e27ccd7d9e6a05b8085cbd438e4bbc65",
    "workspace_edition": "2024"
  },
  "target": {
    "name": "charon-driver",
    "source": "charon/src/bin/charon-driver/main.rs",
    "source_sha256": source_files["charon-driver-main.rs"]["sha256"],
    "modules": modules,
    "explicit_extern_crates": externs,
    "rustc_private_feature_attribute": True,
    "package_level_build_rs": False,
    "test_fixture_build_rs": [
      "charon/tests/cargo/build-script/build.rs",
      "charon/tests/cargo/issue-1298-absolute-path-for-generated-files/build.rs"
    ]
  },
  "fingerprint": {
    "path": "charon/target/release/.fingerprint/charon-dce94fe66085d37d/bin-charon-driver.json",
    "sha256": hashlib.sha256((src / "bin-charon-driver.json").read_bytes()).hexdigest(),
    "features": json.loads(fp["features"]),
    "declared_features": json.loads(fp["declared_features"]),
    "rustflags": fp["rustflags"],
    "release_profile_hash": fp["profile"],
    "cargo_config_hash": fp["config"],
    "cargo_target_compile_kind": fp["compile_kind"],
    "direct_cargo_dependency_count": len(fp["deps"]),
    "persists_full_rustc_argv": False
  },
  "cached_dependencies": {
    "map": "cached-dependency-artifacts.json",
    "count": len(dep_artifacts["deps"]),
    "all_46_have_one_exact_matching_fingerprint": True,
    "artifact_sha_values_joined_from_saved_complete_cache_manifest": True,
    "transitive_proc_macro2": {
      "root_direct_dependency": False,
      "required_by": ["macros", "hax_adt_into"],
      "fingerprint_unit": "proc-macro2-b731dd505951052a",
      "features": ["default", "proc-macro"],
      "profile_hash": 2305346612590964689,
      "artifact_paths": [
        "charon/target/release/deps/libproc_macro2-b731dd505951052a.rlib",
        "charon/target/release/deps/libproc_macro2-b731dd505951052a.rmeta"
      ],
      "receipt": "nested-proc-macro2.raw.json"
    }
  },
  "native_link_evidence": {
    "scan": "build-script-link-directives.json",
    "saved_output_records_with_relevant_directives": link["output_records_with_relevant_directives"],
    "observed_native_link_lib": "cargo:rustc-link-lib=static=psm_s",
    "observed_native_search_path": "/home/dombarker/project-offloads/ZK-v5-formal/toolchains/charon/charon/target/release/build/psm-0054b740d3e1ad34/out",
    "static_archive": {
      "path": "charon/target/release/build/psm-0054b740d3e1ad34/out/libpsm_s.a",
      "size": psm["size"],
      "sha256": psm["sha256"]
    },
    "other_matching_build_outputs": "rustc-cfg directives",
    "sysroot_native_link_requirements": "not fully derived from this Cargo output scan"
  },
  "compile_time_environment": {
    "source_scan_files": ["charon-driver main", "wrapper main", "charon/src/lib.rs"],
    "observed_env_macro": {
      "path": "charon/src/lib.rs",
      "line": 59,
      "expression": "env!(\"CARGO_PKG_VERSION\")",
      "manifest_value": "0.1.223",
      "scope": "charon_lib, a separately compiled cached dependency"
    },
    "driver_main_env_macro_hits": [],
    "captured_build_environment": ["CARGO_HOME", "CARGO_TARGET_DIR"],
    "other_inherited_environment": "not captured by saved build command"
  },
  "known_build_settings": {
    "saved_cargo_command": cmd["cargo_command"],
    "cargo_home": cmd["CARGO_HOME"],
    "target_dir": cmd["CARGO_TARGET_DIR"],
    "release_requested": True,
    "offline_locked_jobs": 1,
    "features_from_fingerprint": ["default", "rustc"],
    "rustflags_from_fingerprint": [],
    "cargo_config_files_checked": [
      "/home/dombarker/.cargo/config",
      "/home/dombarker/.cargo/config.toml",
      "<repo>/.cargo/config",
      "<repo>/.cargo/config.toml",
      "<repo>/charon/.cargo/config",
      "<repo>/charon/.cargo/config.toml"
    ],
    "cargo_config_found": False,
    "rustc_sysroot": cmd["sysroot"],
    "exact_historical_rustc_argv": "unknown; no verbose rustc invocation was saved"
  },
  "stopped_build_v2": {
    "command_receipt": "clone-build-preflight/build-attempt-v2/build-command.json",
    "command_receipt_sha256": hashlib.sha256(cmd_path.read_bytes()).hexdigest(),
    "raw_log": "clone-build-preflight/build-attempt-v2/build.log",
    "raw_log_sha256": hashlib.sha256(log_path.read_bytes()).hexdigest(),
    "raw_log_text": log_path.read_text().strip(),
    "exit_status": result["build_exit_status"],
    "oom": result["oom_or_oom_kill_detected"],
    "first_external_compilation": "proc-macro2 v1.0.96",
    "cache_reconsideration_cause": "unknown from the non-verbose saved log; do not infer cause from presence of cached artifacts",
    "driver_artifact_unchanged": result["candidate_driver_sha256"] == "4cb603ad51132f298a63a9c2a8cc8c629c73edeff22516fbf56ba5decee70938"
  },
  "source_copy_hashes": source_files,
  "no_source_or_cache_mutation_by_this_inventory": True
}
assert len(dep_artifacts["deps"]) == 46
assert len(externs) == 25
(out / "compile-invocation-inventory.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
