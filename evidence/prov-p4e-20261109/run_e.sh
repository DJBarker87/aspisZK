# usage: bash run_e.sh PCWE_E004
cd "$(dirname "$0")"
python3 PCWE_run.py "$1" refextract > "$1.client.log" 2>&1
echo "exit $?" >> "$1.client.log"
