# !/bin/bash

atmo verify -- --emit=dep-info --time-expanded --output-json > time.json
python3 parse_verification.py > time.txt