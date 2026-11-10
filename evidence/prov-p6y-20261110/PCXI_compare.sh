#!/bin/bash
# PCXI_compare.sh: re-derives the 183 receipts; writes PCXI_RECEIPTS_raw.json (reads git HEAD of the worktree; ~60 s)
cd "$(dirname "$0")" && python3 -B -I PCXI_compare.py
