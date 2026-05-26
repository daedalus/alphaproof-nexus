#!/usr/bin/env python3
"""Scrape problem statements from erdosproblems.com and create Lean stubs."""

import os
import re
import sys
import time
import html
import urllib.request
import urllib.error
import concurrent.futures
import json

BASE_URL = "https://www.erdosproblems.com"
WORK_DIR = "/home/dclavijo/my_code/alphaproof-nexus"

def fetch_problem(n):
    """Fetch a problem page and extract the statement."""
    url = f"{BASE_URL}/{n}"
    try:
        req = urllib.request.Request(url, headers={
            'User-Agent': 'Mozilla/5.0 (compatible; AlphaProofNexus; +https://github.com/anomaloco/alphaproof-nexus)'
        })
        with urllib.request.urlopen(req, timeout=15) as resp:
            raw_html = resp.read().decode('utf-8')
    except Exception as e:
        return n, None, str(e)

    # Extract statement from <div id="content">...</div>
    m = re.search(r'<div id="content">(.*?)</div>', raw_html, re.DOTALL)
    if not m:
        return n, None, "content div not found"
    
    raw = m.group(1)
    # Decode HTML entities
    text = html.unescape(raw)
    # Remove any HTML tags (like <a>, <span>)
    text = re.sub(r'<[^>]+>', '', text)
    text = text.strip()
    
    return n, text, None


def make_lean_stub(n, statement):
    """Create a Lean stub file for problem N."""
    # Sanitize statement for embedding in docstring
    statement_clean = statement if statement else "No statement available."
    
    content = f"""import Mathlib

open Set Finset
open scoped BigOperators

/-!
# Erdős Problem {n}

*Reference:* https://www.erdosproblems.com/{n}

{statement_clean}
-/

namespace Erdos{n}

-- EVOLVE-BLOCK-START
-- EVOLVE-BLOCK-END

end Erdos{n}
"""
    return content


def main():
    # Read open problem numbers
    with open('/tmp/open_problems.txt') as f:
        all_nums = [int(line.strip()) for line in f if line.strip()]
    
    # Filter out problems that already have Erdos{N}.lean files
    todo = []
    for n in all_nums:
        fpath = os.path.join(WORK_DIR, 'problems', str(n), f'Erdos{n}.lean')
        if not os.path.exists(fpath):
            todo.append(n)
    
    print(f"Total open problems: {len(all_nums)}")
    print(f"Already have .lean files: {len(all_nums) - len(todo)}")
    print(f"Need to create: {len(todo)}")
    print(f"Sample: {todo[:10]}")
    
    if not todo:
        print("Nothing to do!")
        return
    
    # Scrape with concurrency
    results = {}
    errors = []
    
    with concurrent.futures.ThreadPoolExecutor(max_workers=16) as executor:
        future_to_n = {executor.submit(fetch_problem, n): n for n in todo}
        for future in concurrent.futures.as_completed(future_to_n):
            n = future_to_n[future]
            try:
                n, text, err = future.result()
                if err:
                    errors.append((n, err))
                    print(f"  ERROR #{n}: {err}")
                else:
                    results[n] = text
                    print(f"  OK #{n}: {text[:60]}...")
            except Exception as e:
                errors.append((future_to_n[future], str(e)))
            
            # Small delay to be polite
            time.sleep(0.05)
    
    print(f"\nFetched {len(results)}/{len(todo)} successfully")
    print(f"Errors: {len(errors)}")
    
    # Write Lean files
    created = 0
    for n, statement in results.items():
        dirpath = os.path.join(WORK_DIR, 'problems', str(n))
        os.makedirs(dirpath, exist_ok=True)
        
        # Create population/ directory
        popdir = os.path.join(dirpath, 'population')
        os.makedirs(popdir, exist_ok=True)
        
        # Write Erdos{n}.lean
        fpath = os.path.join(dirpath, f'Erdos{n}.lean')
        if not os.path.exists(fpath):
            with open(fpath, 'w') as f:
                f.write(make_lean_stub(n, statement))
            created += 1
            if created % 50 == 0:
                print(f"  Written {created}/{len(results)} files...")
    
    print(f"\nCreated {created} new Erdos{{N}}.lean files + population/ dirs")
    
    # Save errors for retry
    if errors:
        with open('/tmp/scrape_errors.json', 'w') as f:
            json.dump(errors, f)
        print(f"Errors saved to /tmp/scrape_errors.json")


if __name__ == '__main__':
    main()
