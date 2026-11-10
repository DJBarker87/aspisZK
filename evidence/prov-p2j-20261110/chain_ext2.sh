#!/bin/bash
cd "$(dirname "$0")"
for a in "$@"; do bash run_extract.sh $a < /dev/null; echo "$a $(head -c 150 $a.client.log | head -1)" >> chain_ext2.log; done
echo done >> chain_ext2.log
