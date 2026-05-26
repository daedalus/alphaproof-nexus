#!/usr/bin/env python3
"""Generate initial population members for all 628 Erdős problems."""

import re
import os
import shutil

ERDOS_DIR = "problems/erdos"

def parse_stub(filepath):
    """Parse an Erdos{N}.lean stub and extract metadata."""
    with open(filepath) as f:
        content = f.read()

    ns_match = re.search(r'^namespace\s+(Erdos\d+)', content, re.MULTILINE)
    ns = ns_match.group(1) if ns_match else None

    # Extract full first line for building statement
    stmt_match = re.search(r'^# Erdős Problem (\d+)(?::\s*(.*?))?\s*$', content, re.MULTILINE)
    if not stmt_match:
        stmt_match = re.search(r'^# Erdős Problem (\d+)\s*$', content, re.MULTILINE)

    imports = re.findall(r'^(import\s+\S+)', content, re.MULTILINE)
    opens = re.findall(r'^(open\s.*)', content, re.MULTILINE)

    return {
        "ns": ns,
        "number": ns[5:] if ns else "?",
        "imports": imports or ["import Mathlib"],
        "opens": opens,
        "content": content,
    }

def initial_stub_content(info):
    """Generate member_01_gen1_initial_stub.lean content."""
    ns = info["ns"]
    num = info["number"]
    imports_str = "\n".join(info["imports"])
    opens_lines = info["opens"]
    opens_str = ("\n" + "\n".join(opens_lines)) if opens_lines else ""

    return f'''/-
  Population Member 01 (Gen 1): Initial stub

  Approach: Placeholder — initial proof attempt scaffold.

  Rating (initial): Elo 1200
-/

{imports_str}{opens_str}

namespace {ns}

-- EVOLVE-BLOCK-START

/-- The main conjecture of Erdős Problem {num}. -/
theorem conjecture : True := by
  sorry

-- EVOLVE-BLOCK-END

end {ns}
'''

def main():
    problem_dirs = sorted(
        d for d in os.listdir(ERDOS_DIR)
        if d.isdigit() and os.path.isdir(os.path.join(ERDOS_DIR, d))
    )

    existing = {"1", "25", "364", "634"}
    created = 0
    skipped = 0

    for num in problem_dirs:
        prob_dir = os.path.join(ERDOS_DIR, num)
        pop_dir = os.path.join(prob_dir, "population")

        # Find Erdos{N}.lean
        lean_files = [f for f in os.listdir(prob_dir) if re.match(rf'^Erdos{num}\.lean$', f)]
        if not lean_files:
            print(f"WARN: No Erdos{num}.lean in {prob_dir}")
            skipped += 1
            continue

        stub_file = os.path.join(prob_dir, lean_files[0])
        info = parse_stub(stub_file)

        if not info["ns"]:
            print(f"WARN: No namespace found in {stub_file}")
            skipped += 1
            continue

        # Count existing members
        existing_members = [
            f for f in os.listdir(pop_dir)
            if f.endswith(".lean") and f.startswith("member_")
        ] if os.path.isdir(pop_dir) else []

        if existing_members:
            # For problems with existing population, skip (handled separately)
            print(f"SKIP {num}: already has {len(existing_members)} members")
            skipped += 1
            continue

        # Create population directory
        os.makedirs(pop_dir, exist_ok=True)

        # Write member file
        member_file = os.path.join(pop_dir, "member_01_gen1_initial_stub.lean")
        if not os.path.exists(member_file):
            with open(member_file, "w") as f:
                f.write(initial_stub_content(info))
            created += 1
            print(f"  OK {num}: created member_01_gen1_initial_stub.lean")
        else:
            print(f"  -- {num}: already exists, skipped")
            skipped += 1

    print(f"\nDone: {created} created, {skipped} skipped")

if __name__ == "__main__":
    main()
