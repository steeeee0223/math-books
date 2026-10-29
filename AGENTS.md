# Typst mathematical notation

- Always parenthesize every superscript and subscript operand in Typst mathematics, including single letters, numbers, and symbols. Use `^(...)` and `_(...)`.
- For example, write `H^(q)(X, shf.f)`, `shf.o_(X)`, `x_(i)^(n)`, and `j_(V_(i) ast)`.
- Group nested superscripts and subscripts as well. Keep following function arguments outside the script group: `H^(q)(X, shf.f)`.
- Check new or modified mathematical expressions for unparenthesized scripts before finishing, and compile the affected Typst entry point.
