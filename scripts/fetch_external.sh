#!/bin/sh
# Third-party inputs that are not redistributed here (NASA Open Source Agreement).
set -e
cd "$(dirname "$0")/.."
mkdir -p external
[ -d external/fret ] || git clone --depth 1 https://github.com/NASA-SW-VnV/fret external/fret
echo "FRET case studies in external/fret/caseStudies/LMCPS"
