# !/bin/bash

./run_fmt.sh
atmo verify -- --emit=dep-info
line_count build-tool/lib.d