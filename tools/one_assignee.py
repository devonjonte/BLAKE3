"""Every open issue and pull request has one assignee, the person
whose move is next (AGENTS.md, "One assignee makes the next move").

Run by .github/workflows/one-assignee.yml on every change to an item's
assignees and once a day, and by hand: `python3 tools/one_assignee.py
OWNER/REPO` with a token in GITHUB_TOKEN. An open item with no assignee
gets its author, with a comment; one with several gets a comment asking
for one. Prints what it did; exits 0.
"""
import json
import os
import sys
import urllib.request

NONE = ("Assigned to you, the author, since this had no assignee. The assignee makes the next move: when yours is done, "
        "say what the next move is and assign whoever makes it, or close this.")
MANY = "Several assignees: please leave exactly one, the person whose move is next."


def call(token, method, url, body=None):
    data = None if body is None else json.dumps(body).encode()
    req = urllib.request.Request(url, data=data, method=method,
                                 headers={"Authorization": f"Bearer {token}", "Accept": "application/vnd.github+json",
                                          "Content-Type": "application/json"})
    with urllib.request.urlopen(req, timeout=30) as r:
        return json.load(r) if r.status != 204 else None


def main():
    repo = sys.argv[1]
    token = os.environ["GITHUB_TOKEN"]
    page = 1
    while True:
        items = call(token, "GET", f"https://api.github.com/repos/{repo}/issues?state=open&per_page=100&page={page}")
        if not items:
            break
        for item in items:
            n = item["number"]
            assignees = [a["login"] for a in item["assignees"]]
            if len(assignees) == 1:
                continue
            url = f"https://api.github.com/repos/{repo}/issues/{n}"
            if not assignees:
                author = item["user"]["login"]
                call(token, "POST", f"{url}/assignees", {"assignees": [author]})
                call(token, "POST", f"{url}/comments", {"body": NONE})
                print(f"#{n}: assigned {author}")
            else:
                call(token, "POST", f"{url}/comments", {"body": MANY})
                print(f"#{n}: {len(assignees)} assignees, asked for one")
        page += 1


if __name__ == "__main__":
    main()
