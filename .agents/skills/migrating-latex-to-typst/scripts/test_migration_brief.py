import unittest

from migration_brief import resolve_span, source_outline, typst_outline


class MigrationBriefOutlineTests(unittest.TestCase):
    def test_recognizes_examples_and_leading_numbers_in_titled_source_blocks(self) -> None:
        source = [
            r"\begin{definition}{3. (Ring)}",
            r"\end{definition}",
            r"\begin{example}{5}",
            r"\end{example}",
            r"\begin{remark}{194**}",
            r"\end{remark}",
        ]
        target = [
            '#definition(number: "3", title: [Ring])[',
            '] ',
            '#example(number: 5)[',
            '] ',
            '#remark(number: "194**")[',
            '] ',
        ]

        self.assertEqual(
            [entry.canonical() for entry in source_outline(source, 0, len(source))],
            [entry.canonical() for entry in typst_outline(target)],
        )

    def test_parameter_scan_stops_at_the_current_block(self) -> None:
        target = [
            "#definition(number: none, title: [Ring])[",
            "]",
            "#proposition(number: 24)[",
            "]",
        ]

        entries = typst_outline(target)

        self.assertEqual("", entries[0].number)
        self.assertEqual("24", entries[1].number)

    def test_span_uses_nearest_repeated_start_before_end(self) -> None:
        lines = [
            r"\section{Exercises}",
            r"\chapter{Second}",
            r"\section{Exercises}",
            r"\chapter{Third}",
        ]

        self.assertEqual((2, 3), resolve_span(lines, r"\section{Exercises}", r"\chapter{Third}"))

    def test_span_ignores_repeated_end_before_start(self) -> None:
        lines = [
            r"\section{Exercises}",
            r"\section{Smoothness}",
            r"\section{Exercises}",
        ]

        self.assertEqual((1, 2), resolve_span(lines, r"\section{Smoothness}", r"\section{Exercises}"))


if __name__ == "__main__":
    unittest.main()
