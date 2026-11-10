cd "$(dirname "$0")"
python3 PCWE_run.py PCWE_E002 refextract > PCWE_E002.client.log 2>&1
echo "exit $?" >> PCWE_E002.client.log
