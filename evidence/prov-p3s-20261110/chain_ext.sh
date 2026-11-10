#!/bin/bash
# runs the remaining extraction scopes strictly one after another
cd "$(dirname "$0")"
for a in PCVU_E003 PCVU_E004 PCVU_E005 PCVU_E006; do
  python3 -B PCVU_run.py $a extract > $a.client.log 2>&1
  echo "$a exit $?" >> chain_ext.log
done
echo chain-done >> chain_ext.log
