#!/usr/bin/env python3
"""Isolated actual-source OOM probes. Finite diagnostics, not a security theorem."""
import argparse
import json
import resource
import signal
import subprocess
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("binary", type=Path)
    args = parser.parse_args()
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    results = []
    traces = {}
    for mode, tag, fail_at in [
        ("row", 0, 0), ("row", 1, 0), ("mask", 0, 0), ("mask", 1, 0),
        ("row", 0, 1), ("mask", 0, 1), ("mask", 0, 2), ("mask", 0, 272),
    ]:
        result = subprocess.run([str(args.binary.resolve()), mode, str(tag), str(fail_at)],
                                capture_output=True, text=True, timeout=30)
        record = {"mode": mode, "tag": tag, "fail_at": fail_at,
                  "returncode": result.returncode, "stderr": result.stderr}
        if fail_at:
            assert result.returncode == -signal.SIGABRT, record
            assert "memory allocation of 16384 bytes failed" in result.stderr, record
            assert result.stdout == "", "OOM unexpectedly returned a result"
        else:
            assert result.returncode == 0, record
            lines = result.stdout.splitlines()
            events = [list(map(int, line.split())) for line in lines[1:]]
            assert len(events) == (1 if mode == "row" else 272)
            assert all(size == 16384 and align == 4 and kind in (1, 2)
                       for _, size, align, kind in events)
            traces[mode, tag] = events
            record.update(header=lines[0], events=events)
        results.append(record)
    assert traces["row", 0] == traces["row", 1]
    assert traces["mask", 0] == traces["mask", 1]
    print(json.dumps({"status": "finite diagnostic only", "cases": results}, indent=2))


if __name__ == "__main__":
    main()
