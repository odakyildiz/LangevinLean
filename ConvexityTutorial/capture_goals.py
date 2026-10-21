#!/usr/bin/env python3
"""Capture genuine Lean goal states around source-aligned tutorial steps.

The original Lean files are never edited. Copies in a temporary directory gain
marker tactics and Lean's built-in ``trace_state`` before and after each complete
tactic step. Only successfully checked copies contribute states to the output.
Lean emits trace messages separately from marker messages, so their source
positions, rather than stdout order, identify the corresponding captured state.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import tempfile
from collections import defaultdict
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
MARKER = "CONVEXITY_TUTORIAL"
TRACE_IMPORT = "import Mathlib.Tactic.Trace"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def lesson_steps(notes):
    steps = []
    seen = set()
    for lesson in notes["lessons"]:
        path = lesson["file"]
        for step in lesson["steps"]:
            identifier = step["id"]
            require(isinstance(identifier, str) and identifier and "|" not in identifier,
                    f"Invalid goal-capture step ID: {identifier!r}")
            require(identifier not in seen, f"Duplicate tutorial step ID: {identifier}")
            seen.add(identifier)
            steps.append({**step, "file": path, "lesson": lesson["id"],
                          "theorem": lesson.get("theorem")})
    return steps


def state_kind(step):
    return step.get("kind", step.get("type", "tactic"))


def step_ranges(steps):
    """Only source boundaries and IDs affect capture; prose can evolve freely."""
    return [{"id": step["id"], "file": step["file"], "start": step["start"],
             "end": step["end"], "kind": state_kind(step)} for step in steps]


def instrument(source, steps):
    """Return the checked copy and positions of all inserted trace tactics."""
    lines = source.splitlines()
    events = defaultdict(list)
    for step in steps:
        start, end = step["start"], step["end"]
        require(type(start) is int and type(end) is int
                and 1 <= start <= end <= len(lines),
                f"Invalid source range for {step['id']}: {start}–{end}")
        if state_kind(step) == "declaration":
            continue
        first = lines[start - 1]
        require(first.strip() and not first.lstrip().startswith(("--", "/-", "·", "|", "_ ")),
                f"Step {step['id']} must start at a complete tactic command, not a comment, "
                "branch delimiter, or calc continuation")
        indent = first[:len(first) - len(first.lstrip())]
        require(indent, f"Tactic step {step['id']} starts at top level")
        events[start].append(("before", step, indent))
        events[end + 1].append(("after", step, indent))

    imports = [i + 1 for i, line in enumerate(lines) if line.startswith("import ")]
    require(imports, "A tutorial source file must have an import header")
    header_end = max(imports)
    output = []
    positions = {}
    for number in range(1, len(lines) + 2):
        # At adjacent step boundaries, capture the finished step first. Nested
        # captures are supported when their ranges are complete tactic blocks.
        events_here = sorted(events[number], key=lambda item: (
            item[0] != "after", -len(item[2]) if item[0] == "after" else len(item[2])))
        for phase, step, indent in events_here:
            key = step["id"], phase
            start_marker = f"{MARKER}|{step['id']}|{phase}|start"
            end_marker = f"{MARKER}|{step['id']}|{phase}|end"
            marker_line = len(output) + 1
            output.append(indent + "trace " + json.dumps(start_marker))
            state_line = len(output) + 1
            output.append(indent + "trace_state")
            end_line = len(output) + 1
            output.append(indent + "trace " + json.dumps(end_marker))
            positions[key] = {
                "markerLine": marker_line, "stateLine": state_line, "endLine": end_line,
                "startMarker": start_marker, "endMarker": end_marker,
            }
        if number <= len(lines):
            output.append(lines[number - 1])
        if number == header_end:
            if TRACE_IMPORT not in lines:
                output.append(TRACE_IMPORT)
            output.extend(["", "set_option linter.unusedTactic false", ""])
    return "\n".join(output) + "\n", positions


def run(command, *, timeout):
    result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True, timeout=timeout)
    if result.returncode:
        raise RuntimeError("Command failed: " + " ".join(map(str, command)) + "\n"
                           + result.stdout + result.stderr)
    return result


def parse_messages(output):
    messages = []
    for line in output.splitlines():
        if not line.strip():
            continue
        try:
            message = json.loads(line)
        except json.JSONDecodeError as error:
            raise RuntimeError("Lean did not emit JSON diagnostics: " + line) from error
        require(isinstance(message, dict), "Unexpected Lean diagnostic format")
        if message.get("severity") == "error":
            raise RuntimeError("Instrumented proof has an error: " + message.get("data", ""))
        messages.append(message)
    return messages


def extract_states(messages, positions):
    by_line = defaultdict(list)
    for message in messages:
        if message.get("pos"):
            by_line[message["pos"]["line"]].append(message)
    states = {}
    for (identifier, phase), location in positions.items():
        start = by_line[location["markerLine"]]
        end = by_line[location["endLine"]]
        require(any(message.get("data") == location["startMarker"] for message in start),
                f"Missing before-state marker for {identifier}.{phase}")
        require(any(message.get("data") == location["endMarker"] for message in end),
                f"Missing after-state marker for {identifier}.{phase}")
        traces = [message for message in by_line[location["stateLine"]]
                  if message.get("kind") == "trace"]
        require(len(traces) == 1,
                f"Expected one genuine Lean state for {identifier}.{phase}, got {len(traces)}")
        raw = traces[0].get("data")
        require(isinstance(raw, str), f"Non-text Lean goal state for {identifier}.{phase}")
        states.setdefault(identifier, {})[phase] = {
            "raw": raw, "noGoals": raw == "", "traceLine": location["stateLine"],
        }
    return states


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--notes", type=Path, default=HERE / "lesson_notes.json")
    parser.add_argument("--output", type=Path, default=HERE / "proof_states.json")
    parser.add_argument("--timeout", type=int, default=300,
                        help="Maximum seconds for each Lean/build command")
    parser.add_argument("--skip-build", action="store_true",
                        help="Use already built tutorial imports (normal runs rebuild first)")
    args = parser.parse_args()
    annotation_bytes = args.notes.read_bytes()
    notes = json.loads(annotation_bytes)
    steps = lesson_steps(notes)
    require(steps, "The tutorial has no annotated steps")
    by_file = defaultdict(list)
    for step in steps:
        by_file[step["file"]].append(step)
    sources = {}
    hashes = {}
    for path in by_file:
        require(not Path(path).is_absolute() and ".." not in Path(path).parts,
                f"Tutorial source must be a repository-relative path: {path}")
        data = (ROOT / path).read_bytes()
        sources[path] = data.decode("utf-8")
        hashes[path] = hashlib.sha256(data).hexdigest()
    if not args.skip_build:
        targets = [str(Path(path).with_suffix("")).replace("/", ".") for path in by_file]
        run(["lake", "build", *targets], timeout=args.timeout)
    version = run(["lake", "env", "lean", "--version"], timeout=args.timeout).stdout.strip()
    captured = {}
    with tempfile.TemporaryDirectory(prefix="convexity-goals-") as temporary:
        temporary_path = Path(temporary)
        for index, (path, file_steps) in enumerate(by_file.items(), 1):
            copy, positions = instrument(sources[path], file_steps)
            target = temporary_path / f"Capture{index}.lean"
            target.write_text(copy)
            result = run(["lake", "env", "lean", "--json", "-Dpp.unicode.fun=true",
                          "-R", str(temporary_path), str(target)],
                         timeout=args.timeout)
            states = extract_states(parse_messages(result.stdout), positions)
            for step in file_steps:
                identifier = step["id"]
                common = {"kind": state_kind(step), "file": path, "start": step["start"],
                          "end": step["end"], "verified": True}
                if state_kind(step) == "declaration":
                    captured[identifier] = {
                        **common, "before": {"kind": "declaration"},
                        "after": {"kind": "declaration"},
                        "declaration": "\n".join(sources[path].splitlines()
                                                   [step["start"] - 1:step["end"]]),
                    }
                else:
                    require(identifier in states and set(states[identifier]) == {"before", "after"},
                            f"Missing captured states for {identifier}")
                    captured[identifier] = {**common, **states[identifier]}
            # All imported definitions came from the build before instrumentation;
            # prevent a concurrent source edit from leaving misleading source hashes.
            require(hashlib.sha256((ROOT / path).read_bytes()).hexdigest() == hashes[path],
                    f"Source changed while capturing states: {path}; rerun the capture")
    require(set(captured) == {step["id"] for step in steps}, "Captured-state coverage mismatch")
    for path, expected in hashes.items():
        require(hashlib.sha256((ROOT / path).read_bytes()).hexdigest() == expected,
                f"Source changed during capture: {path}; rerun the capture")
    current_steps = lesson_steps(json.loads(args.notes.read_bytes()))
    require(step_ranges(current_steps) == step_ranges(steps),
            "Lesson step boundaries changed during capture; rerun the capture")
    output = {
        "formatVersion": 1, "sourceHashes": hashes, "steps": captured,
        "capture": {"leanVersion": version, "method": "Lean trace_state in checked temporary copies",
                    "originalSourcesEdited": False, "importsRebuilt": not args.skip_build,
                    "stepRangesHash": hashlib.sha256(json.dumps(step_ranges(steps),
                        ensure_ascii=False, sort_keys=True).encode()).hexdigest(),
                    "prettyPrintOptions": {"pp.unicode.fun": True}},
    }
    args.output.write_text(json.dumps(output, ensure_ascii=False, indent=2) + "\n")
    tactic_count = sum(state_kind(step) != "declaration" for step in steps)
    print(f"Captured {2 * tactic_count} genuine Lean states for {tactic_count} tactic steps; "
          f"verified {len(steps) - tactic_count} declaration steps in {len(by_file)} source files")


if __name__ == "__main__":
    main()
