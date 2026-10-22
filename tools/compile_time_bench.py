#!/usr/bin/env python3
"""Measure Nim compile-time checking for a fixed Eponym corpus.

CI measures a PR target and candidate on the same runner to avoid comparing
absolute timings across machines. Per-corpus measurements are saved as JSON.
"""
from __future__ import annotations

import argparse
import json
import platform
import statistics
import subprocess
import sys
import tempfile
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BUDGET_PATH = ROOT / "bench" / "compile_time_budget.json"
NAT_LEMMAS_FIXTURE = '''import eponym_mac

eponymBlock:
  import "../lib/nat_lemmas.ep"
'''


def run_process(command: list[str], cwd: Path, timeout: int = 600) -> float:
    started = time.perf_counter()
    completed = subprocess.run(
        command, cwd=cwd, text=True, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, timeout=timeout, check=False,
    )
    elapsed = time.perf_counter() - started
    if completed.returncode != 0:
        raise RuntimeError(
            f"command failed ({completed.returncode}): {' '.join(command)}\n"
            f"{completed.stdout}"
        )
    return elapsed


def nim_version() -> str:
    result = subprocess.run(
        ["nim", "--version"], text=True, capture_output=True, check=True
    )
    return result.stdout.splitlines()[0]


def measure(repo: Path, budget: dict) -> dict:
    actual = nim_version()
    version = actual.split()[3]
    expected = budget["measurement"]["compiler"].split()[-1]
    if version != expected:
        raise RuntimeError(f"expected Nim {expected}; found {actual}")

    samples: dict[str, list[float]] = {}
    for corpus in budget["corpora"]:
        name = corpus["name"]
        fixture = repo / corpus["path"]
        generated = corpus.get("generateIfMissing", False) and not fixture.exists()
        if generated:
            fixture.write_text(NAT_LEMMAS_FIXTURE)
        samples[name] = []
        try:
            for sample_no in range(corpus["runs"]):
                with tempfile.TemporaryDirectory(prefix="eponym-compile-time-") as tmp:
                    command = [
                        "nim", "check", "--hints:off", "--verbosity:0",
                        f"--maxLoopIterationsVM:{corpus['vmLoopLimit']}",
                        f"--path:{repo / 'src'}",
                        f"--path:{repo / 'src' / 'eponym'}",
                        f"--nimcache:{Path(tmp) / 'nimcache'}",
                        str(fixture),
                    ]
                    elapsed = run_process(command, repo)
                    samples[name].append(elapsed)
                    print(
                        f"{name} run {sample_no + 1}/{corpus['runs']}: "
                        f"{elapsed:.3f}s", flush=True,
                    )
        finally:
            if generated:
                fixture.unlink(missing_ok=True)

    commit = subprocess.run(
        ["git", "rev-parse", "HEAD"], cwd=repo, text=True,
        capture_output=True, check=True,
    ).stdout.strip()
    return {
        "schema": 1,
        "commit": commit,
        "toolchain": actual,
        "platform": platform.platform(),
        "corpus": {
            name: {
                "samplesSeconds": values,
                "medianSeconds": statistics.median(values),
            }
            for name, values in samples.items()
        },
    }


def is_regression(
    baseline: float,
    current: float,
    max_relative_regression: float,
    min_absolute_regression: float,
) -> bool:
    return (
        current > baseline * (1.0 + max_relative_regression)
        and current - baseline > min_absolute_regression
    )


def self_test(budget: dict) -> None:
    policy = budget["measurement"]
    relative = policy["maxRelativeRegression"]
    absolute = policy["minimumAbsoluteRegressionSeconds"]
    baseline = 20.0
    within_budget = baseline * (1.0 + relative / 2.0)
    synthetic_regression = max(
        baseline * (1.0 + relative + 0.15),
        baseline + absolute * 2.0,
    )
    assert not is_regression(baseline, within_budget, relative, absolute)
    assert is_regression(baseline, synthetic_regression, relative, absolute)
    print(
        f"synthetic regression check passed: "
        f"{(synthetic_regression / baseline - 1.0) * 100.0:.0f}% growth is "
        "flagged; a smaller change remains within the noise budget"
    )


def compare(current: dict, baseline: dict, budget: dict) -> bool:
    if current["toolchain"] != baseline["toolchain"]:
        raise RuntimeError("cannot compare measurements from different Nim toolchains")
    if current["platform"] != baseline["platform"]:
        raise RuntimeError("cannot compare measurements from different platforms")
    policy = budget["measurement"]
    relative = policy["maxRelativeRegression"]
    absolute = policy["minimumAbsoluteRegressionSeconds"]
    failed = False
    print(
        f"comparison: {current['commit'][:12]} vs "
        f"{baseline['commit'][:12]} on {current['platform']}"
    )
    for corpus in budget["corpora"]:
        name = corpus["name"]
        before = baseline["corpus"][name]["medianSeconds"]
        after = current["corpus"][name]["medianSeconds"]
        change = (after / before - 1.0) * 100.0 if before else float("inf")
        regressed = is_regression(before, after, relative, absolute)
        marker = "REGRESSION" if regressed else "within budget"
        print(
            f"  {name}: {before:.3f}s -> {after:.3f}s "
            f"({change:+.1f}%) — {marker}"
        )
        failed = failed or regressed
    return failed


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=ROOT)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--compare", type=Path)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()

    budget = json.loads(BUDGET_PATH.read_text())
    if args.self_test:
        self_test(budget)
        return 0

    current = measure(args.repo_root.resolve(), budget)
    rendered = json.dumps(current, indent=2) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered)
    print(rendered, end="")

    if args.compare:
        baseline = json.loads(args.compare.read_text())
        if compare(current, baseline, budget):
            print(
                "compile-time budget exceeded: investigate the regression or "
                "record an evidence-backed budget change",
                file=sys.stderr,
            )
            return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
