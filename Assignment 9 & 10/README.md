# Haskell: Functional Programming Basics & Effects

**CPSC [course] · Chapman University · Spring 2026**

Two assignments covering core Haskell concepts — recursion, pattern matching, higher-order functions, and monadic effects.

---

## Assignments

### Part 1 — FP Basics (`hw-fp-basics.hs`)

| Problem | Topic | Description |
|---------|-------|-------------|
| 1 | Pattern matching & recursion | `skip1` — keep every other element starting from the first |
| 2 | Recursion | `mySum` — sum a list of integers recursively |
| 3 | Higher-order functions | `countPasses` — count how many predicates a value satisfies |
| 4 | Functor | `shoutInside` — uppercase a `Maybe String` using `fmap` |
| 5 | Merge sort | `merge` and `mergeSort` — recursive merge sort over any `Ord` type |

### Part 2 — Effects (`hw-effects.hs`)

| Problem | Topic | Description |
|---------|-------|-------------|
| 1 | Functor over `Maybe` | `cleanLine` / `cleanMaybeName` — normalize whitespace and uppercase |
| 2 | Functor over lists | `tagAll` — label every item in a list using `fmap` |
| 3 | `Maybe` monad | `firstKnownEmail` — chain two lookups, short-circuit on failure |
| 4 | List monad | `pairsThatSum` — all ordered pairs summing to a target via `do` + `guard` |
| 5 | `Either` | `login` — report `MissingUser` or `BadPassword` with informative errors |
| 6 | IO | `runCleanerOnce` — read a line, clean it, print it |
| 7 | Recursive IO | `askNonEmpty` — keep prompting until the user enters a non-empty answer |

---

## Files

| File | Description |
|------|-------------|
| `hw-fp-basics.hs` | Recursion, pattern matching, higher-order functions, Functor, merge sort |
| `hw-effects.hs` | Functors, Maybe / Either / list monads, IO effects |

---

## Tools & Technologies

- **GHC** — Glasgow Haskell Compiler
- **GHCi** — Interactive Haskell REPL for quick checks

---

## Getting Started

### Prerequisites

- GHC 9.x ([GHCup](https://www.haskell.org/ghcup/) recommended)

### Running

Load either file in GHCi and run the quick checks from the assignment header:

```bash
ghci hw-fp-basics.hs
```

```haskell
skip1 [1,2,3,4,5]           -- [1,3,5]
mySum [3,1,4]                -- 8
countPasses [even,(>10),odd] 14  -- 2
shoutInside (Just "hi")      -- Just "HI"
mergeSort [3,1,4,1,5]        -- [1,1,3,4,5]
```

```bash
ghci hw-effects.hs
```

```haskell
cleanLine "  hello   haskell  "        -- "HELLO HASKELL"
cleanMaybeName (Just "  ada  lovelace ") -- Just "ADA LOVELACE"
tagAll "fruit" ["apple", "pear"]       -- ["fruit: apple","fruit: pear"]
firstKnownEmail 1 sampleNames sampleEmails -- Just "ada@example.com"
pairsThatSum 5 [1,2,3,4]               -- [(1,4),(2,3),(3,2),(4,1)]
login "ada" "lambda" samplePasswords   -- Right "Welcome, ada!"
login "ada" "wrong"  samplePasswords   -- Left BadPassword
```

---

## Author

**Ethan Tapia** · B.S. Computer Science, Chapman University '26
