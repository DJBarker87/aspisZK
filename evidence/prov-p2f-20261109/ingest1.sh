#!/bin/bash
cd "$(dirname "$0")"
mkdir -p gen/logs
for pair in B7:L001 B1:L002 B2:L003 B3:L004 B4:L005 B5:L006 B6:L007 H4:L008 H1:L009 H2:L010 H3:L011; do
  bk=${pair%%:*}; at=PCUF_${pair##*:}
  xz -dc $at/stdout.log.xz > gen/logs/probe_$bk.log
  echo "== $bk"
  python3 -B PCUF_gen.py ingest 2 $bk gen/logs/probe_$bk.log
done
