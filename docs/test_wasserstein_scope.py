"""Completion requires faithful source endpoints and independently compiled clients."""
import copy
import importlib.util
from pathlib import Path
import unittest

SPEC = importlib.util.spec_from_file_location(
    "wasserstein_coverage", Path(__file__).resolve().parents[1] / "scripts/verify-wasserstein-mixing.py")
COVERAGE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(COVERAGE)


class ScopeTests(unittest.TestCase):
    def fixture(self):
        return dict(
            results=[dict(id="theorem:main", kind="theorem", status="proved",
                          proofs=[dict(file=COVERAGE.ENDPOINT_FILE, declaration="bias_bound")])],
            required_endpoints=[dict(id=ident, source_label=label, status="proved",
                                     file=COVERAGE.ENDPOINT_FILE, declaration=name)
                                for ident, (label, name) in COVERAGE.SOURCE_ENDPOINTS.items()],
            pending_foundations=[],
            compiled_source_audit=dict(status="proved", axioms=sorted(COVERAGE.ALLOWED_AXIOMS),
                                       declarations=[name for _, name in COVERAGE.SOURCE_ENDPOINTS.values()]))

    def test_actual_source_endpoints_and_compiled_audit_are_complete(self):
        self.assertTrue(COVERAGE.completion_state(self.fixture())[0])

    def test_conditional_endpoint_cannot_be_relabelled_complete(self):
        data = self.fixture()
        data["required_endpoints"][0]["declaration"] = "conditional_bias_bound"
        self.assertFalse(COVERAGE.completion_state(data)[0])

    def test_pending_foundation_blocks_named_proved_endpoints(self):
        data = self.fixture()
        data["pending_foundations"] = [dict(id="realization", status="pending")]
        self.assertEqual(COVERAGE.completion_state(data)[1], ["realization"])
        self.assertFalse(COVERAGE.completion_state(data)[0])

    def test_missing_or_unproved_compiled_audit_blocks_completion(self):
        for value in ({}, dict(status="pending")):
            data = self.fixture()
            data["compiled_source_audit"] = value
            self.assertFalse(COVERAGE.completion_state(data)[0])

    def test_proof_hole_axiom_blocks_completion(self):
        data = self.fixture()
        data["compiled_source_audit"]["axioms"].append("sorryAx")
        self.assertFalse(COVERAGE.completion_state(data)[0])

    def test_missing_source_proof_blocks_completion(self):
        data = self.fixture()
        data["results"][0]["proofs"] = []
        self.assertFalse(COVERAGE.completion_state(data)[0])

    def test_missing_source_endpoint_blocks_completion(self):
        data = self.fixture()
        data["required_endpoints"].pop()
        self.assertFalse(COVERAGE.completion_state(data)[0])

    def test_wrong_source_location_blocks_completion(self):
        data = copy.deepcopy(self.fixture())
        data["required_endpoints"][0]["source_label"] = "invented-label"
        self.assertFalse(COVERAGE.completion_state(data)[0])


if __name__ == "__main__":
    unittest.main()
