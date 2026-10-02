#!/usr/bin/env python3
"""Bounded read-only R349/installed Charon source provenance probes."""
import datetime, hashlib, json, pathlib, subprocess, time

out = pathlib.Path(__file__).resolve().parent / "probes"
out.mkdir(exist_ok=True)
host = "dombarker@100.108.41.90"
ssh_opts = ["-o", "BatchMode=yes", "-o", "ConnectTimeout=5", "-o", "StrictHostKeyChecking=no", "-o", "UserKnownHostsFile=/dev/null"]
image = "ef96e46342a4"
root = "/home/dombarker/project-offloads/aspis-r349-output-name-alpha-candidate-20261002-a"
cmds = [
    ("r349-link", ["ssh", *ssh_opts, host,
      "set +e; ls -ld " + root + "/src/charon; printf 'readlink='; readlink " + root + "/src/charon; printf 'resolved='; readlink -f " + root + "/src/charon; test -e " + root + "/src/charon; rc=$?; printf 'target_exists_exit=%s\\n' \"$rc\"; exit 0"]),
    ("image-package-query", ["ssh", *ssh_opts, host,
      "docker run --rm --network none --memory=512m --memory-swap=512m --pids-limit=32 --entrypoint bash " + image +
      " -lc 'set -e; cd /work/src 2>/dev/null || true; printf \"package_query=\"; opam exec -- ocamlfind query charon; printf \"package_version=\"; opam exec -- ocamlfind query -format %v charon; printf \"installed_source_stat=\"; stat -c %F\\\\\\\\ %s\\\\\\\\ %n /home/opam/.opam/5.2/lib/charon/NameMatcher.ml; printf \"installed_source_realpath=\"; readlink -f /home/opam/.opam/5.2/lib/charon/NameMatcher.ml; sha256sum /home/opam/.opam/5.2/lib/charon/NameMatcher.ml; printf \"meta_head:\\n\"; sed -n \"1,12p\" /home/opam/.opam/5.2/lib/charon/META'" ]),
    ("image-installed-name-matcher", ["ssh", *ssh_opts, host,
      "docker run --rm --network none --memory=512m --memory-swap=512m --pids-limit=32 --entrypoint cat " + image +
      " /home/opam/.opam/5.2/lib/charon/NameMatcher.ml"]),
    ("pinned-name-matcher-hash", ["ssh", *ssh_opts, host,
      "sha256sum /home/dombarker/project-offloads/ZK-v5-formal/toolchains/charon/charon-ml/src/NameMatcher.ml"]),
]
manifest = {"captured_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(), "host": host,
            "container_image": image, "read_only_caps_for_image_commands": {"memory_max": "512m", "memory_swap_total": "512m (zero swap allowance)", "pids": 32, "network": "none"},
            "probes": []}
for name, argv in cmds:
    start = time.monotonic()
    p = subprocess.run(argv, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    elapsed = time.monotonic() - start
    base = out / name
    base.with_suffix(".stdout").write_bytes(p.stdout)
    base.with_suffix(".stderr").write_bytes(p.stderr)
    rec = {"name": name, "argv": argv, "exit_status": p.returncode, "elapsed_seconds": elapsed,
           "stdout_path": str(base.with_suffix(".stdout")), "stdout_sha256": hashlib.sha256(p.stdout).hexdigest(),
           "stdout_bytes": len(p.stdout), "stderr_path": str(base.with_suffix(".stderr")),
           "stderr_sha256": hashlib.sha256(p.stderr).hexdigest(), "stderr_bytes": len(p.stderr)}
    if name == "image-installed-name-matcher" and p.returncode == 0:
        src = out / "installed-NameMatcher.ml"
        src.write_bytes(p.stdout)
        rec["saved_source_path"] = str(src)
        rec["saved_source_sha256"] = hashlib.sha256(p.stdout).hexdigest()
    manifest["probes"].append(rec)
(out / "receipt.json").write_text(json.dumps(manifest, indent=2) + "\n")
print(json.dumps(manifest, indent=2))
