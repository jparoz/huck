# Huck

A purely functional programming language,
bringing type-safety, purity, and functional idioms to the Lua ecosystem.

# Overview

This is a personal project of mine,
and is not currently ready for production use!

# Roadmap (rough)

## 0.1
- [x] Basic literal datatypes (`Int`, `Float`, `String`)
- [x] Lists `[1, 2, 3]`
- [x] Tuples `(1.23, "hi")`
- [x] Unit type `()`
- [x] Hindley-Milner style typechecker
- [x] Operator precedence declarations #huck/syntax
- [x] Explicit type annotations
- [x] Custom type definitions
- [x] Let bindings
- [x] If-then-else expressions
- [x] Case expressions

## 0.2
- [x] Imports of Huck modules
- [x] Imports of Lua modules (foreign)
- [x] Structured name resolution
- [x] Prelude
- [ ] More complete testing
- [ ] More readable and comprehensive example code

## 0.3
- [ ] Internal compiler work: overhaul AST
- [ ] Tuple function arguments for uncurried functions
- [ ] Type-level binops
- [ ] Type constructor binops
- [ ] Backtick binops (e.g. `3 \`elem\` [1, 2, 3]`)

## 0.4
- [ ] Record types
- [ ] Ability to create mixed Lua tables (i.e. both a map and a list)

## 0.5
- [ ] Improved errors
- [ ] Exhaustiveness checking in definitions and case statements

## 0.6
- [ ] Lazy values (optional)

## 0.7
- [ ] Type classes

## 0.8
- [ ] Optimisations

## 0.9
- [ ] REPL
