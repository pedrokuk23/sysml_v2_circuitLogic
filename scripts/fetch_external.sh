#!/bin/sh
# Third-party inputs that are not redistributed here (NASA FRET repository, Apache License 2.0).
set -e
cd "$(dirname "$0")/.."
mkdir -p external
FRET_COMMIT=cf0f913cc15c41705e803593297e89cd6056b839   # commit used for every result of the paper
[ -d external/fret ] || { git clone -q https://github.com/NASA-SW-VnV/fret external/fret && git -C external/fret checkout -q $FRET_COMMIT; }
echo "FRET case studies in external/fret/caseStudies (LMCPS, LiftPlusCruise)"
