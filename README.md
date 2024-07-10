## Dependencies

Make sure LLVM is installed: `clang --version`

## Usage

The API is on the bottom of the file `src/mila_lang/codegen.clj`, including automatic tests.

## Generating parse table

You can generate the parse table from the grammar file `attributed-grammar.edn` [here](https://pages.fit.cvut.cz/peckato1/parsingtbl/):

`(mila-lang.parser.core/copy-grammar)` copies the grammar into clipboard, then click the button under the parse
table to copy the grammar as JSON to clipboard, that one you paste into `parse-table.json`.
