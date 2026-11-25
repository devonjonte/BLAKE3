import io
import unittest

import close_release_milestone as mod


class CloseReleaseMilestoneTests(unittest.TestCase):
    def test_version_from_tag(self):
        self.assertEqual(mod.version_from_tag("v0.11.0+deadbeef"), "0.11.0")
        self.assertEqual(mod.version_from_tag("v0.10.0"), "0.10.0")
        self.assertEqual(mod.version_from_tag("0.11.0-rc.1+abc1234"), "0.11.0-rc.1")
        with self.assertRaises(ValueError):
            mod.version_from_tag("not-a-tag")

    def test_closes_completed_milestone(self):
        calls = []

        def fake_request(method, url, token, payload=None):
            calls.append((method, url, token, payload))
            if method == "GET":
                return [
                    {"number": 1, "title": "post 0.10, pre 1.0", "open_issues": 5, "closed_issues": 20},
                    {"number": 4, "title": "0.11.0", "open_issues": 0, "closed_issues": 12},
                ]
            return {"number": 4, "state": "closed"}

        out = io.StringIO()
        status = mod.close_completed_milestone("v0.11.0+1b6f3178", "owner/repo", "tok", request=fake_request, out=out)
        self.assertEqual(status, "closed")
        self.assertIn("closed #4 (0.11.0)", out.getvalue())
        self.assertEqual(len(calls), 2)
        self.assertEqual(calls[1][0], "PATCH")
        self.assertTrue(calls[1][1].endswith("/repos/owner/repo/milestones/4"))
        self.assertEqual(calls[1][3], {"state": "closed"})

    def test_matches_v_prefixed_milestone_title(self):
        calls = []

        def fake_request(method, url, token, payload=None):
            calls.append((method, url, payload))
            if method == "GET":
                return [{"number": 7, "title": "v0.11.0", "open_issues": 0, "closed_issues": 3}]
            return {"number": 7, "state": "closed"}

        out = io.StringIO()
        status = mod.close_completed_milestone("v0.11.0+abcdef", "owner/repo", "tok", request=fake_request, out=out)
        self.assertEqual(status, "closed")
        self.assertEqual(calls[1][0], "PATCH")

    def test_leaves_milestone_with_open_issues_open(self):
        calls = []

        def fake_request(method, url, token, payload=None):
            calls.append(method)
            return [{"number": 4, "title": "0.11.0", "open_issues": 2, "closed_issues": 10}]

        out = io.StringIO()
        status = mod.close_completed_milestone("v0.11.0+abcdef", "owner/repo", "tok", request=fake_request, out=out)
        self.assertEqual(status, "still_open")
        self.assertIn("still has 2 open issue(s)", out.getvalue())
        self.assertEqual(calls, ["GET"])

    def test_missing_or_already_closed_milestone_is_noop(self):
        calls = []

        def fake_request(method, url, token, payload=None):
            calls.append(method)
            return [{"number": 1, "title": "post 0.10, pre 1.0", "open_issues": 0, "closed_issues": 10}]

        out = io.StringIO()
        status = mod.close_completed_milestone("v0.11.0+abcdef", "owner/repo", "tok", request=fake_request, out=out)
        self.assertEqual(status, "not_found")
        self.assertIn("nothing to close", out.getvalue())
        self.assertEqual(calls, ["GET"])


if __name__ == "__main__":
    unittest.main()
