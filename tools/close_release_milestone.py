#!/usr/bin/env python3
"""Close a release's completed GitHub milestone after its published artifacts pass.

Usage:
    python3 tools/close_release_milestone.py TAG [--repo OWNER/NAME]

Extracts the release version from TAG (e.g. `v0.11.0+deadbeef` -> `0.11.0`),
finds any open GitHub milestone titled `0.11.0` or `v0.11.0`, and closes it
if and only if `open_issues == 0`. Uses only the Python standard library and
`GITHUB_TOKEN` (or `GH_TOKEN`) so it runs cleanly in GitHub Actions without
extra packages.
"""

import json
import os
import re
import sys
import urllib.request

TAG_VERSION = re.compile(r"^v?(\d+\.\d+\.\d+(?:-[0-9A-Za-z.-]+)?)(?:\+[0-9A-Za-z.-]+)?$")


def version_from_tag(tag):
    """Return the semantic version part of a release tag, or raise ValueError."""
    m = TAG_VERSION.match(tag.strip())
    if not m:
        raise ValueError(f"not a release tag: {tag!r}")
    return m.group(1)


def github_request(method, url, token, payload=None):
    headers = {
        "Accept": "application/vnd.github+json",
        "X-GitHub-Api-Version": "2022-11-28",
        "User-Agent": "blake3-servil-release-milestone",
    }
    if token:
        headers["Authorization"] = f"Bearer {token}"
    data = None
    if payload is not None:
        data = json.dumps(payload).encode("utf-8")
        headers["Content-Type"] = "application/json"
    req = urllib.request.Request(url, data=data, headers=headers, method=method)
    with urllib.request.urlopen(req, timeout=30) as resp:
        return json.loads(resp.read().decode("utf-8"))


def close_completed_milestone(tag, repo, token, api_base="https://api.github.com", request=github_request, out=None):
    """Close the open milestone matching `tag`'s version when it has zero open issues.

    Returns one of: `"closed"`, `"still_open"`, or `"not_found"`.
    """
    out = out or sys.stdout
    version = version_from_tag(tag)
    wanted = {version, f"v{version}"}
    match = None
    page = 1
    while True:
        milestones = request("GET", f"{api_base}/repos/{repo}/milestones?state=open&per_page=100&page={page}", token)
        match = next((m for m in milestones if m.get("title") in wanted), None)
        if match is not None or len(milestones) < 100:
            break
        page += 1
    if match is None:
        print(f"milestone: no open milestone matching {version!r} in {repo}; nothing to close", file=out)
        return "not_found"
    number = match["number"]
    title = match["title"]
    open_issues = int(match.get("open_issues", 0))
    closed_issues = int(match.get("closed_issues", 0))
    if open_issues > 0:
        print(f"milestone: #{number} ({title}) still has {open_issues} open issue(s); leaving open", file=out)
        return "still_open"
    request("PATCH", f"{api_base}/repos/{repo}/milestones/{number}", token, {"state": "closed"})
    print(f"milestone: closed #{number} ({title}) (0 open, {closed_issues} closed)", file=out)
    return "closed"


def main(argv=None):
    argv = list(sys.argv[1:] if argv is None else argv)
    repo = os.environ.get("GITHUB_REPOSITORY", "")
    tag = None
    i = 0
    while i < len(argv):
        if argv[i] == "--repo" and i + 1 < len(argv):
            repo = argv[i + 1]
            i += 2
        elif tag is None and not argv[i].startswith("-"):
            tag = argv[i]
            i += 1
        else:
            sys.exit(f"usage: {sys.argv[0]} TAG [--repo OWNER/NAME]")
    if not tag or not repo:
        sys.exit(f"usage: {sys.argv[0]} TAG [--repo OWNER/NAME] (or set GITHUB_REPOSITORY)")
    token = os.environ.get("GITHUB_TOKEN") or os.environ.get("GH_TOKEN") or ""
    if not token:
        sys.exit("GITHUB_TOKEN or GH_TOKEN is required to close a milestone")
    close_completed_milestone(tag, repo, token)


if __name__ == "__main__":
    main()
