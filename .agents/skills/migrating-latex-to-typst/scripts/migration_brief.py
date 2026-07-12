#!/usr/bin/env python3
"""Report source/target boundaries for LaTeX-to-Typst migration work."""

from __future__ import annotations

import argparse
import re
from dataclasses import dataclass
from pathlib import Path


SOURCE_ENV_RE = re.compile(
    r"\\begin\{(?P<kind>definition\*?|proposition|lemma|theorem|corollary|remark\*?|example|exercise|exe|proof|notation|fact|nt)\}"
    r"(?:\{(?P<title>[^}]*)\})?"
)
TYPST_BLOCK_RE = re.compile(
    r"^\s*#(?P<kind>definition|proposition|lemma|theorem|corollary|remark|note|exercise|proof|notation)(?:-box)?\b"
)
NUMBER_RE = re.compile(r"\bnumber:\s*(?P<number>[0-9]+(?:\.[0-9A-Za-z]+)?)")
TITLE_RE = re.compile(r'title:\s*"(?P<title>[^"]+)"')
FACT_TITLE_RE = re.compile(r"\bFact\s+(?P<number>[0-9]+(?:\.[0-9A-Za-z]+)?)\b")
COMMENTED_SOURCE_RE = re.compile(r"^\s*//\s*\\begin\{(?P<kind>[^}]+)\}(?:\{(?P<title>[^}]*)\})?")
LATEX_RESIDUE_RE = re.compile(
    r"\\(?:begin|end|item|text|textit|textbf|frac|xrightarrow|xhookrightarrow|widetilde|mathcal|mathfrak|operatorname|Spec|Proj|OO|FF|GG|MOD|qcoh|coh)\b"
)


@dataclass(frozen=True)
class Entry:
    line: int
    kind: str
    title: str = ""
    number: str = ""

    def label(self) -> str:
        bits = [self.kind]
        if self.number:
            bits.append(self.number)
        if self.title and self.title != self.number:
            bits.append(self.title)
        return " ".join(bits)

    def canonical(self) -> tuple[str, str]:
        kind_map = {
            "fact": "lemma",
            "exe": "exercise",
            "definition*": "definition",
            "remark*": "remark",
            "nt": "note",
        }
        return (kind_map.get(self.kind, self.kind), self.number)


def read_lines(path: Path) -> list[str]:
    return path.read_text(encoding="utf-8").splitlines()


def find_marker(lines: list[str], marker: str, *, start_at: int = 0) -> int:
    for index in range(start_at, len(lines)):
        if marker in lines[index]:
            return index
    raise SystemExit(f"marker not found: {marker}")


def source_outline(lines: list[str], start: int, end: int) -> list[Entry]:
    entries: list[Entry] = []
    for index in range(start, end):
        match = SOURCE_ENV_RE.search(lines[index])
        if not match:
            continue
        title = match.group("title") or ""
        number = title if re.fullmatch(r"[0-9]+(?:\.[0-9A-Za-z]+)?", title) else ""
        entries.append(Entry(index + 1, match.group("kind"), title, number))
    return entries


def typst_outline(lines: list[str]) -> list[Entry]:
    entries: list[Entry] = []
    for index, line in enumerate(lines):
        if line.lstrip().startswith("//"):
            continue
        match = TYPST_BLOCK_RE.search(line)
        if not match:
            continue
        window_lines = [line]
        open_paren = line.find("(")
        open_bracket = line.find("[")
        has_parameter_list = open_paren >= 0 and (open_bracket < 0 or open_paren < open_bracket)
        if has_parameter_list:
            for next_line in lines[index + 1 : min(index + 8, len(lines))]:
                window_lines.append(next_line)
                if ")[" in next_line:
                    break
        window = "\n".join(window_lines)
        number_match = NUMBER_RE.search(window)
        title_match = TITLE_RE.search(window)
        title = title_match.group("title") if title_match else ""
        fact_title_match = FACT_TITLE_RE.search(title)
        entries.append(
            Entry(
                index + 1,
                match.group("kind"),
                title=title,
                number=(
                    number_match.group("number")
                    if number_match
                    else fact_title_match.group("number")
                    if fact_title_match
                    else ""
                ),
            )
        )
    return entries


def first_commented_source(lines: list[str]) -> Entry | None:
    for index, line in enumerate(lines):
        match = COMMENTED_SOURCE_RE.search(line)
        if match:
            title = match.group("title") or ""
            number = title if re.fullmatch(r"[0-9]+(?:\.[0-9A-Za-z]+)?", title) else ""
            return Entry(index + 1, match.group("kind"), title, number)
    return None


def live_latex_residue(lines: list[str]) -> list[tuple[int, str]]:
    hits: list[tuple[int, str]] = []
    for index, line in enumerate(lines):
        if line.lstrip().startswith("//"):
            continue
        if LATEX_RESIDUE_RE.search(line):
            hits.append((index + 1, line.strip()))
    return hits


def next_after_last_target(source_entries: list[Entry], target_entries: list[Entry]) -> Entry | None:
    last_numbered_target = next((entry for entry in reversed(target_entries) if entry.number), None)
    if not last_numbered_target:
        return source_entries[0] if source_entries else None

    last_seen = -1
    for index, entry in enumerate(source_entries):
        if entry.number != last_numbered_target.number:
            continue
        if entry.canonical() == last_numbered_target.canonical():
            last_seen = index
            break
        if last_seen < 0:
            last_seen = index

    has_live_proof_after_last_number = any(
        entry.kind == "proof"
        for entry in target_entries[target_entries.index(last_numbered_target) + 1 :]
    )
    if has_live_proof_after_last_number:
        while last_seen + 1 < len(source_entries) and source_entries[last_seen + 1].kind == "proof":
            last_seen += 1

    if last_seen + 1 < len(source_entries):
        return source_entries[last_seen + 1]
    return None


def completion_errors(source_entries: list[Entry], target_entries: list[Entry], residue: list[tuple[int, str]]) -> list[str]:
    errors: list[str] = []
    source_shape = [entry.canonical() for entry in source_entries]
    target_shape = [entry.canonical() for entry in target_entries]
    if source_shape != target_shape:
        errors.append("source and target outlines differ")
    if residue:
        errors.append("live LaTeX residue detected")
    return errors


def print_entries(title: str, entries: list[Entry], *, limit: int = 24) -> None:
    print(f"\n{title}")
    if not entries:
        print("  (none)")
        return
    for entry in entries[:limit]:
        print(f"  line {entry.line}: {entry.label()}")
    if len(entries) > limit:
        print(f"  ... {len(entries) - limit} more")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--target", type=Path, required=True)
    parser.add_argument("--start", required=True, help="literal marker where the LaTeX source span starts")
    parser.add_argument("--end", required=True, help="literal marker where the LaTeX source span ends")
    parser.add_argument("--expect-complete", action="store_true", help="fail if source and target outlines do not match")
    args = parser.parse_args()

    source_lines = read_lines(args.source)
    target_lines = read_lines(args.target)

    start = find_marker(source_lines, args.start)
    end = find_marker(source_lines, args.end, start_at=start + 1)
    source_entries = source_outline(source_lines, start, end)
    target_entries = typst_outline(target_lines)
    commented = first_commented_source(target_lines)
    residue = live_latex_residue(target_lines)
    next_entry = next_after_last_target(source_entries, target_entries)

    print("Migration brief")
    print(f"  source: {args.source}")
    print(f"  target: {args.target}")
    print(f"  source span: lines {start + 1}-{end} ({args.start} -> before {args.end})")
    if target_entries:
        print(f"  last live Typst block: line {target_entries[-1].line}: {target_entries[-1].label()}")
    if next_entry:
        print(f"  next source environment after live target outline: line {next_entry.line}: {next_entry.label()}")
    if commented:
        print(f"  first commented backlog marker in target: line {commented.line}: {commented.label()}")

    print_entries("Source outline", source_entries)
    print_entries("Live Typst outline", target_entries)

    print("\nLive LaTeX residue")
    if residue:
        for line_no, text in residue[:20]:
            print(f"  line {line_no}: {text}")
        if len(residue) > 20:
            print(f"  ... {len(residue) - 20} more")
    else:
        print("  none detected by static pattern")

    print("\nRecommended next move")
    if commented:
        print(f"  Convert or replace the commented backlog starting at target line {commented.line}, beginning with source {commented.label()}.")
    elif next_entry:
        print(f"  Append the source block at line {next_entry.line}: {next_entry.label()}.")
    else:
        print("  No next source block was inferred; inspect source and target outlines manually.")
    if args.expect_complete:
        errors = completion_errors(source_entries, target_entries, residue)
        print("\nCompletion check")
        if errors:
            for error in errors:
                print(f"  FAIL: {error}")
            return 1
        print("  PASS: source and target outlines match with no live LaTeX residue")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
