#!/usr/bin/env python3

from __future__ import annotations

import hashlib
import re
import unittest
from pathlib import Path

import generate_yoshida_even_sparse_congruence as generator


class DominanceModuleGenerationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.repo_root = Path(__file__).resolve().parents[1]
        cls.result = generator.audit(cls.repo_root)
        cls.modules = generator.dominance_generated_modules(cls.result)

    def test_serial_module_graph_and_hashes(self) -> None:
        self.assertEqual(generator.BLOCK_CHECKS_PER_MODULE, 8)
        self.assertEqual(generator.ROWS_PER_MODULE, 10)
        self.assertEqual(len(self.modules), 96 + 20 + 1)

        paths = [module["path"] for module in self.modules]
        self.assertEqual(len(paths), len(set(paths)))
        for index, module in enumerate(self.modules):
            content = module["content"]
            self.assertEqual(
                module["sha256"],
                hashlib.sha256(content.encode("utf-8")).hexdigest(),
            )
            if index == 0:
                predecessor = (
                    "ArithmeticHodge.Analysis.YoshidaEvenSparseCongruenceDominanceData"
                )
            else:
                predecessor = paths[index - 1].removesuffix(".lean").replace("/", ".")
            imports = re.findall(r"^import (.+)$", content, flags=re.MULTILINE)
            self.assertEqual(imports, [predecessor])

    def test_every_block_and_row_theorem_is_emitted_once(self) -> None:
        contents = "\n".join(module["content"] for module in self.modules)
        blocks = re.findall(
            r"^theorem evenSparseDominanceBlock_row(\d{3})_(\d{3})_le",
            contents,
            flags=re.MULTILINE,
        )
        expected_blocks = [
            (f"{row:03d}", f"{block:03d}")
            for row, budgets in enumerate(self.result["block_budgets"])
            for block in range(len(budgets))
        ]
        self.assertEqual(blocks, expected_blocks)
        self.assertEqual(len(blocks), 762)

        entries_rows = re.findall(
            r"^theorem evenSparseWeightedDominanceEntries_row(\d{3}) :",
            contents,
            flags=re.MULTILINE,
        )
        public_rows = re.findall(
            r"^theorem evenSparseWeightedDominance_row(\d{3}) :",
            contents,
            flags=re.MULTILINE,
        )
        expected_rows = [f"{row:03d}" for row in range(200)]
        self.assertEqual(entries_rows, expected_rows)
        self.assertEqual(public_rows, expected_rows)

        final = self.modules[-1]["content"]
        self.assertIn("theorem evenSparseWeightedDominanceEntries :", final)
        self.assertIn("theorem evenSparseWeightedDominance :", final)

    def test_module_batch_parser(self) -> None:
        module_count = len(self.modules)
        last = module_count - 1
        self.assertEqual(generator.parse_module_batch("0:5", module_count), (0, 5))
        self.assertEqual(
            generator.parse_module_batch(f"{last}:1", module_count), (last, 1)
        )
        invalid_batches = (
            "",
            "0",
            "-1:1",
            "0:0",
            f"{last}:2",
            f"{module_count}:1",
        )
        for invalid in invalid_batches:
            with self.subTest(invalid=invalid):
                with self.assertRaises(ValueError):
                    generator.parse_module_batch(invalid, module_count)


if __name__ == "__main__":
    unittest.main()
