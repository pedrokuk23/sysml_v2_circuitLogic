#!/bin/sh
# Validate the SysML v2 models with the SysML v2 Pilot Implementation (release 0.63.1).
# The jar ships with the Jupyter SysML kernel (e.g. `conda install -c conda-forge jupyter-sysml-kernel=0.63.1`);
# set SYSML_KERNEL_DIR to the folder that contains jupyter-sysml-kernel-0.63.1-all.jar and sysml.library/.
set -e
K=${SYSML_KERNEL_DIR:?set SYSML_KERNEL_DIR}
HERE=$(cd "$(dirname "$0")" && pwd)
javac -cp "$K/jupyter-sysml-kernel-0.63.1-all.jar" -d "$HERE" "$HERE/Validate.java"
for m in "$HERE"/../models/*.sysml; do
  echo "== $m"
  java -cp "$K/jupyter-sysml-kernel-0.63.1-all.jar:$HERE" Validate "$K/sysml.library/" "$m" 2>&1 | grep -v "^Reading\|^log4j\|^Picked"
done
