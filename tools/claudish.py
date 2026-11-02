"""Warns on the habits of prose that sound like a language model (Claudish)
or work against AGENTS.md's "Communication". A warning is a reason to
reread the sentence; judgment decides what changes, often nothing. The
script always exits 0. Its rules are this file and nowhere else: when the
rules and AGENTS.md disagree, change this file.

    python3 tools/claudish.py [--kind commit|comment|pr|doc] FILE...
    python3 tools/claudish.py --kind commit - < message

A Markdown file is read whole, outside code blocks and tables; any other
file's comment lines; `-` is standard input. The kind sets a length
budget (a commit's subject 72 characters and its body 60 words; a comment
150 words; a pull request 250; a document's paragraphs 120 each) and
defaults to `comment` for standard input and `doc` for a file.

What it warns about, and why:
- A sentence over 28 words: the reader holds too much at once.
- A sentence chained by 4 or more colons and semicolons.
- Two parentheses, or a semicolon, in one sentence: two sentences folded
  into one.
- A colon followed by more than 12 words: a clause restating the one
  before it.
- Three or more items joined by commas and "and" or "or" in running
  text: the triplet is a rhythm; a list that matters is a list.
- A contrast built on a negation ("X, not Y", "rather than", "instead
  of", "no longer", "not only"): say what is.
- A prohibition ("never", "don't", "avoid"): a rule steers best by the
  habit to keep (target fixation).
- A mid-sentence dash: an aside dressed as emphasis.
- Metadiscourse, a sentence about the text ("Note that", "In short",
  "This file holds", "To be clear").
- Filler ("simply", "really", "actually") and stock vocabulary
  ("robust", "load-bearing", "delve", "the shape of"...).
- A bold label opening a bullet or paragraph: a heading where a sentence
  belongs.

The output ends with the passage of AGENTS.md (the one beside this
script) behind each rule that fired, found by a phrase of it, with its
line; a phrase gone from AGENTS.md stops the script, so the two change
together.
"""
import os
import re
import sys

RULES = [
    ("contrast", r"\bnot\b[^.;:]{1,60}?,\s*but\b|,\s+not\s+(?:a |an |the )?[\w-]+[,.;]|\brather than\b|\binstead of\b|\bno longer\b|\bnot (?:only|just|merely)\b"),
    ("prohibition", r"\b(?:never|don't|do not|avoid(?:s|ed|ing)?|refrain\w*)\b"),
    ("vocabulary", r"\bload-bearing\b|\bspine\b|\bseams?\b|\bcrisp\w*|\bgenuine(?:ly)?\b|\bhonest(?:ly)?\b|\bthe shape of\b|\bdelve\w*|\bthe real (?:question|issue|work|cost|win)\b|\btapestry\b|\bnuanced?\b|\brobust(?:ly)?\b|\bseamless(?:ly)?\b|\bleverage\b|\bcomprehensive\b|\bholistic\b|\bcrucial\b|\bvital\b|\bearn(?:s|ed)? its place\b|\brides beside\b|\bspeaks? for (?:itself|themselves)\b|\bbehind (?:a|the) door\b|\bthe whole of\b|\bas it stands\b|\bwhat matters\b|\bthe point is\b|\bat the end of the day\b|\bgoing forward\b|\bmake no mistake\b"),
    ("filler", r"\b(?:simply|just|really|actually|quite|very|basically|essentially|truly|exactly|of course|needless to say|arguably|notably|importantly)\b"),
    ("metadiscourse", r"\b(?:note that|it is worth|it's worth|worth noting|in other words|to be clear|to be fair|here's the thing|that said|with that said|in short|in summary|to summarize|that is,)\b"),
    ("dash", r"\w\s?—\s?\w|\s--\s"),
]
ABOUT_THE_TEXT = re.compile(
    r"^(?:this (?:file|document|section|paragraph|note|page|entry|list|table|commit|change|pull request|pr|issue|comment|message)\b"
    r"|what follows|in what follows|the following|as follows|here is|here are|let me|i want to|i would like to|i'd like to"
    r"|first,|second,|third,|finally,|lastly,)",
    re.I,
)
SERIES = re.compile(r"[^,;:.]+,\s+[^,;:.]+,\s+(?:and|or)\s+[^,;:.]+")
BOLD_LABEL = re.compile(r"^(?:(?:[-*+]|\d+\.)\s+)?\*\*[^*]+[:.]?\*\*")
LONG_WORDS, CHAIN_MARKS, COLON_WORDS = 28, 4, 12
BUDGETS = {"commit": None, "comment": 150, "pr": 250, "doc": None}
PARAGRAPH_WORDS = 120

# Each rule's passage in AGENTS.md's "Communication", found by a phrase of it.
WHY = {
    "contrast": "Phrase positively or neutrally",
    "prohibition": "A rule names the habit to keep",
    "long": "The reader has limited working memory",
    "chained": "The reader has limited working memory",
    "folded": "The reader has limited working memory",
    "colon": "The reader has limited working memory",
    "length": "The reader has limited working memory",
    "filler": "Sand off filler words",
    "metadiscourse": "Trim metadiscourse",
    "about the text": "Trim metadiscourse",
    "vocabulary": "warns on a few patterns that sound like a language model",
    "dash": "warns on a few patterns that sound like a language model",
    "series": "warns on a few patterns that sound like a language model",
    "bold label": "warns on a few patterns that sound like a language model",
}
AGENTS = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "AGENTS.md")


def passages():
    """Each rule's passage: (AGENTS.md's line number, its text). Stops when
    a phrase is gone from AGENTS.md: the two change together."""
    lines = open(AGENTS).read().split("\n")
    found = {}
    for rule, phrase in WHY.items():
        at = [n for n, line in enumerate(lines, 1) if phrase in line]
        assert at, f"claudish: AGENTS.md no longer says {phrase!r}: change WHY with it"
        found[rule] = (at[0], lines[at[0] - 1].strip().lstrip("-0123456789. "))
    return found


def words(s):
    return len(re.findall(r"[A-Za-z0-9`'’\-]+", s))


def prose(path, text):
    """The text's prose lines as (line number, text), an empty one
    between paragraphs: a Markdown file's outside code blocks and tables,
    any other file's comment lines. A list item or heading starts a
    paragraph of its own; the signature line is none."""
    markdown = path == "-" or path.endswith(".md")
    fenced = False
    for n, line in enumerate(text.split("\n"), 1):
        s = line.strip()
        if re.match(r"—\s*\S+ \S+\s*$", s):
            yield n, ""
            continue
        if markdown:
            if s.startswith("```"):
                fenced = not fenced
            elif not fenced and not s.startswith("|") and not line.startswith("    "):
                if re.match(r"(?:[-*+]|\d+\.)\s|#", s):
                    yield n, ""
                yield n, s
        else:
            m = re.match(r"(?://[/!]?|#|\*|/\*)\s?(.*)", s)
            yield n, (m.group(1) if m else "")


def paragraphs(lines):
    """Paragraphs as (first line, text), each joined across its lines."""
    parts, start = [], None
    for n, s in list(lines) + [(0, "")]:
        if not s:
            if parts:
                yield start, " ".join(parts)
            parts, start = [], None
            continue
        start = start or n
        parts.append(s)


def sentences(text):
    text = re.sub(r"`[^`]*`", "`x`", text)
    text = re.sub(r"\([^)]*\)", lambda m: m.group(0).replace(".", "·"), text)
    for sentence in re.split(r"(?<=[.!?])\s+(?=[A-Z(`*\"'\[])", text):
        if sentence:
            yield sentence


def lint(path, text, kind, fired):
    found = []
    said = " ".join(s for _, s in prose(path, text))
    if kind == "commit":
        subject, _, body = text.strip().partition("\n")
        if len(subject) > 72:
            found.append((1, "length", f"subject {len(subject)} characters (72)"))
        if words(body) > 60:
            found.append((2, "length", f"body {words(body)} words (60)"))
    elif BUDGETS[kind] and words(said) > BUDGETS[kind]:
        found.append((1, "length", f"{words(said)} words ({BUDGETS[kind]} for a {kind})"))
    for line, p in paragraphs(prose(path, text)):
        heading = p.startswith("#")
        item = bool(re.match(r"(?:[-*+]|\d+\.)\s", p))
        if heading:
            continue
        if kind == "doc" and not item and words(p) > PARAGRAPH_WORDS:
            found.append((line, "length", f"paragraph of {words(p)} words ({PARAGRAPH_WORDS})"))
        if BOLD_LABEL.match(p):
            found.append((line, "bold label", p[:60]))
        for s in sentences(re.sub(r"^(?:[-*+]|\d+\.)\s+", "", p)):
            hits = [(name, m.group(0)) for name, rule in RULES for m in re.finditer(rule, s, re.I)]
            n = words(s)
            if n > LONG_WORDS:
                hits.append(("long", f"{n} words"))
            marks = len(re.findall(r"[:;]\s", s))
            if marks >= CHAIN_MARKS:
                hits.append(("chained", f"{marks} colons and semicolons"))
            if s.count("(") >= 2 or ";" in s:
                hits.append(("folded", "two sentences in one"))
            m = re.search(r":\s+(.*)$", s)
            if m and words(m.group(1)) > COLON_WORDS and not re.match(r"\s*[-*`]", m.group(1)):
                hits.append(("colon", f"{words(m.group(1))} words after it"))
            if not item and SERIES.search(s):
                hits.append(("series", "three items in a sentence"))
            if ABOUT_THE_TEXT.match(s):
                hits.append(("about the text", s[:40]))
            for name, what in hits:
                found.append((line, name, f"{what!r} in: {s[:100]}{'...' if len(s) > 100 else ''}"))
    for line, name, what in found:
        fired.add(name)
        print(f"{path}:{line}: {name}: {what}")
    return len(found)


def main(argv):
    kind = None
    if argv[:1] == ["--kind"]:
        kind, argv = argv[1], argv[2:]
        assert kind in BUDGETS, f"--kind takes one of {', '.join(BUDGETS)}"
    why = passages()
    fired = set()
    total = 0
    for path in argv or ["-"]:
        text = sys.stdin.read() if path == "-" else open(path).read()
        total += lint(path, text, kind or ("comment" if path == "-" else "doc"), fired)
    if fired:
        print("Why, in AGENTS.md's \"Communication\":")
        for line, text in sorted({why[name] for name in fired}):
            rules = ", ".join(n for n in WHY if n in fired and why[n] == (line, text))
            print(f"  {rules}: AGENTS.md:{line}: {text[:140]}{'...' if len(text) > 140 else ''}")
    print(f"{total} warnings: each a reason to reread, none an error", file=sys.stderr)


if __name__ == "__main__":
    main(sys.argv[1:])
