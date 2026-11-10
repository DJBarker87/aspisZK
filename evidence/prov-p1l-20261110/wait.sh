#!/bin/bash
# usage: bash wait.sh RUN  (runs extract, waits, prints summary)
cd "$(dirname "$0")"
bash run_extract.sh "$1"
tail -c 400 "$1.client.log"
