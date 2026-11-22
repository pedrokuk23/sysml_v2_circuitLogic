#!/bin/sh
# Dump the Pilot Implementation's abstract syntax tree of every model (release 0.63.1) to results/reference/ast/,
# for the front-end cross-check tests/ast_check.py. Same jar and library as validate.sh.
set -e
K=${SYSML_KERNEL_DIR:?set SYSML_KERNEL_DIR}
HERE=$(cd "$(dirname "$0")" && pwd)
OUT="$HERE/../results/reference/ast"; mkdir -p "$OUT"
javac -cp "$K/jupyter-sysml-kernel-0.63.1-all.jar" -d "$HERE" "$HERE/DumpAst.java"
for m in "$HERE"/../models/*.sysml; do
  java -cp "$K/jupyter-sysml-kernel-0.63.1-all.jar:$HERE" DumpAst "$K/sysml.library/" "$m" "$OUT/$(basename "$m" .sysml).json" 2>&1 \
    | grep -v "^Reading\|^log4j\|^Picked" || true
done
