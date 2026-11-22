# Reproducible environment for the translation-fidelity tests and the compiler (Kind 2 and Java are optional).
#   docker build -t sysmlc . && docker run --rm sysmlc            # runs the 68 tests
#   docker run --rm -v $PWD/results:/repo/results sysmlc sh scripts/run_all.sh
FROM python:3.13-slim
RUN apt-get update && apt-get install -y --no-install-recommends graphviz && rm -rf /var/lib/apt/lists/*
WORKDIR /repo
COPY requirements.txt .
RUN pip install --no-cache-dir -r requirements.txt
COPY . .
CMD ["python3", "tests/run_tests.py"]
