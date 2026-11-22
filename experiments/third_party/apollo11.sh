#!/bin/sh
# Requirement-layer circuit reading of the Airbus Apollo 11 SysML v2 model (third-party, MPL-2.0; not redistributed).
# Clones the model at the commit analysed, concatenates its 28 files, parses them with the SysML v2 Pilot
# Implementation 0.63.1 (validation/DumpAst.java), and runs sysmlc/requirements_layer.py on the syntax tree.
#   SYSML_KERNEL_DIR=... sh experiments/third_party/apollo11.sh [OUTDIR]
set -e
K=${SYSML_KERNEL_DIR:?set SYSML_KERNEL_DIR}
HERE=$(cd "$(dirname "$0")" && pwd); ROOT=$(cd "$HERE/../.." && pwd)
OUT=${1:-$ROOT/results/reference/third_party}; mkdir -p "$OUT"
W=$(mktemp -d)
git clone -q https://github.com/airbus/apollo-11-sysml-v2 "$W/apollo"
git -C "$W/apollo" checkout -q 0e8a7d6790cfa7e15b991eb745e9a38f9bed0474
find "$W/apollo" -name "*.sysml" | sort | xargs cat > "$W/apollo11_all.sysml"
javac -cp "$K/jupyter-sysml-kernel-0.63.1-all.jar" -d "$W" "$ROOT/validation/DumpAst.java"
java -Xmx6g -cp "$K/jupyter-sysml-kernel-0.63.1-all.jar:$W" DumpAst "$K/sysml.library/" "$W/apollo11_all.sysml" "$W/apollo11_ast.json" 2>&1 \
  | grep -v "^Reading\|^log4j\|^Picked" || true
python3 "$ROOT/sysmlc/requirements_layer.py" "$W/apollo11_ast.json" "$OUT/apollo11_requirements_layer.json"
rm -rf "$W"
