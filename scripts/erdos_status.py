#!/usr/bin/env python3
"""Fetch Erdős problem status from erdosproblems.com (via GitHub YAML database)."""

import argparse
import json
import re
import sys
from urllib.request import urlopen, Request
from urllib.error import URLError

YAML_URL = "https://raw.githubusercontent.com/teorth/erdosproblems/main/data/problems.yaml"
HEADERS = {"User-Agent": "erdos_status/1.0"}

SOLVED_STATES = {
    "proved", "disproved", "solved",
    "proved (lean)", "disproved (lean)", "solved (lean)",
    "verifiable", "falsifiable", "decidable",
}

def try_import_yaml():
    try:
        import yaml as _y
        return _y
    except ImportError:
        return None


def fetch_yaml():
    resp = urlopen(Request(YAML_URL, headers=HEADERS), timeout=30)
    return resp.read().decode()


def parse_yaml(text):
    yaml = try_import_yaml()
    if yaml:
        return yaml.safe_load(text)

    # Minimal YAML list-of-dicts parser (no nesting beyond dict values, no arrays)
    problems = []
    current = None
    key = None
    val_buffer = None
    in_list = False
    list_items = []

    for line in text.splitlines():
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        if line.startswith("- "):
            if current and key:
                if in_list:
                    current[key] = list_items
                    in_list = False
                    list_items = []
                else:
                    current[key] = (val_buffer or "").strip()
                val_buffer = None
            if current:
                problems.append(current)
            current = {}
            key, _, val = line[2:].strip().partition(":")
            key = key.strip()
            val = val.strip()
            if val:
                val = val.strip("\"'")
                current[key] = val
                key = None
            else:
                val_buffer = ""
        elif current is not None and line.startswith("  "):
            stripped = line.strip()
            if stripped.startswith("- "):
                if not in_list and key:
                    current[key] = []
                    in_list = True
                item = stripped[2:].strip().strip("\"'")
                list_items.append(item)
            elif ":" in stripped:
                if in_list:
                    current[key] = list_items
                    in_list = False
                    list_items = []
                if val_buffer is not None and val_buffer.strip():
                    current[key] = val_buffer.strip()
                k, _, v = stripped.partition(":")
                key = k.strip()
                val = v.strip().strip("\"'")
                val_buffer = val if not val else None
                if val:
                    current[key] = val
            elif val_buffer is not None:
                val_buffer += "\n" + stripped
    if current:
        if in_list:
            current[key] = list_items
        elif key and val_buffer is not None:
            current[key] = val_buffer.strip()
        problems.append(current)
    return problems


def normalize_state(s):
    return (s or "").strip().lower()


def is_open(state):
    ns = normalize_state(state)
    return ns == "open"


def is_solved(state):
    ns = normalize_state(state)
    return ns in SOLVED_STATES


def display_status(state):
    ns = normalize_state(state)
    if ns == "open":
        return "OPEN", "\U0001f7e2"
    elif ns in SOLVED_STATES:
        return "SOLVED", "\U0001f534"
    return state.upper() if state else "UNKNOWN", "\u26aa"


def main():
    parser = argparse.ArgumentParser(
        description="Fetch Erdős problem status from erdosproblems.com (via GitHub YAML)"
    )
    parser.add_argument("ids", nargs="*", type=int, help="Problem IDs to fetch (default: all)")
    parser.add_argument("-r", "--range", nargs=2, type=int, metavar=("START", "END"),
                        help="Range of problem IDs (inclusive)")
    parser.add_argument("--open-only", action="store_true", help="Only show open problems")
    parser.add_argument("--solved-only", action="store_true", help="Only show solved problems")
    parser.add_argument("--tags", action="store_true", help="Show problem tags")
    parser.add_argument("--formalized", action="store_true", help="Show formalization status")
    parser.add_argument("--json", action="store_true", help="Output as JSON")
    parser.add_argument("--stats", action="store_true", help="Show summary stats and exit")
    parser.add_argument("--repo", action="store_true",
                        help="Filter to problems matching local repo dirs")
    parser.add_argument("--no-fetch", action="store_true",
                        help="Read cached YAML from stdin instead of fetching")
    args = parser.parse_args()

    # --- fetch data ---
    if args.no_fetch:
        text = sys.stdin.read()
    else:
        try:
            text = fetch_yaml()
        except URLError as e:
            print(f"Error fetching YAML: {e}", file=sys.stderr)
            sys.exit(1)

    problems = parse_yaml(text)

    # --- normalize ---
    by_number = {}
    for p in problems:
        n = int(p.get("number", 0))
        by_number[n] = p

    ids = args.ids
    if args.range:
        start, end = args.range
        ids = list(range(start, end + 1))
    elif args.repo:
        import pathlib
        repo = pathlib.Path(__file__).resolve().parent.parent
        ids = set()
        for d in repo.iterdir():
            m = re.match(r'Erdos(\d+)', d.name)
            if m:
                ids.add(int(m.group(1)))
        ids = sorted(ids)
    elif ids:
        pass  # explicit IDs
    else:
        ids = sorted(by_number.keys())

    filtered = [by_number[n] for n in ids if n in by_number]

    if args.open_only:
        filtered = [p for p in filtered if is_open(p.get("status", {}).get("state", ""))]
    if args.solved_only:
        filtered = [p for p in filtered if is_solved(p.get("status", {}).get("state", ""))]

    # --- stats ---
    total_all = len(problems)
    open_count = sum(1 for p in problems if is_open(p.get("status", {}).get("state", "")))
    solved_count = sum(1 for p in problems if is_solved(p.get("status", {}).get("state", "")))
    pct = round(100 * solved_count / total_all) if total_all else 0

    # --- output ---
    if args.json:
        out = {
            "stats": {"total": total_all, "open": open_count, "solved": solved_count, "pct": pct},
            "problems": [],
        }
        for p in filtered:
            st = p.get("status", {})
            state = st.get("state", "")
            status_label, _ = display_status(state)
            prize = p.get("prize", "") or ""
            if prize.lower() == "no":
                prize = ""
            entry = {
                "id": int(p["number"]),
                "status": status_label,
                "state": state,
                "prize": prize,
                "title": p.get("title", ""),
                "tags": p.get("tags", []),
                "formalized": p.get("formalized", {}).get("state", ""),
                "oeis": p.get("oeis", []),
                "comments": p.get("comments", ""),
            }
            out["problems"].append(entry)
        print(json.dumps(out, indent=2))
        return

    if args.stats:
        print(f"erdosproblems.com (GitHub YAML): {total_all} problems")
        print(f"  Open:     {open_count} ({round(100 * open_count / total_all)}%)")
        print(f"  Solved:   {solved_count} ({pct}%)")
        if not args.no_fetch:
            print(f"\n  (Data from github.com/teorth/erdosproblems)")
        return

    # --- table ---
    print(f"erdosproblems.com: {total_all} problems, {solved_count} solved ({pct}%)\n")

    for p in filtered:
        st = p.get("status", {})
        state = st.get("state", "")
        label, icon = display_status(state)
        n = int(p["number"])
        prize = p.get("prize", "") or ""
        if prize.lower() == "no":
            prize = ""
        title = p.get("title", "") or ""
        title_short = (title[:76] + "..") if len(title) > 78 else title

        extras = []
        if args.tags:
            tags = p.get("tags", [])
            if tags:
                extras.append(f"[{', '.join(tags)}]")
        if args.formalized:
            fstate = p.get("formalized", {}).get("state", "")
            if fstate:
                extras.append(f"formalized={fstate}")

        suffix = f"  {'  '.join(extras)}" if extras else ""
        print(f"  {icon} #{n:<5} {label:<8} {prize:<12} {title_short}{suffix}")

    print(f"\n  {len(filtered)} problem(s)")


if __name__ == "__main__":
    main()
